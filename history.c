#include <ctype.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef _WIN32
#define snprintf _snprintf
#define msleep Sleep
#else
#include <sys/time.h>
#include <termios.h>
#include <unistd.h>
#define msleep(ms)                                                                                                             \
	{                                                                                                                          \
		struct timespec tv;                                                                                                    \
		tv.tv_sec = (ms) / 1000;                                                                                               \
		tv.tv_nsec = ((ms) % 1000) * 1000 * 1000;                                                                              \
		nanosleep(&tv, &tv);                                                                                                   \
	}
#endif

#include "history.h"
#include "utf8.h"

typedef struct cmd_ cmd;

struct cmd_ {
	cmd *prev, *next;
	char *line;
};

static cmd *g_history = NULL;
static FILE *g_histfile = NULL;
static char *g_last = NULL;
static const char **key_words = NULL;

#define bold "\e[1m"
#define normal "\e[0m"
#define blink "\e[5m"
#define negative "\e[7m"
#define italic "\e[3m"
#define red "\e[31m"

#define SAVE "\e[s"
#define UNSAVE "\e[u"

int history_getch(void)
{
	struct termios oldattr, newattr;
	tcgetattr(STDIN_FILENO, &oldattr);
	newattr = oldattr;
	newattr.c_lflag &= ~(ICANON | ECHO);
	tcsetattr(STDIN_FILENO, TCSANOW, &newattr);
	int ch = getc_utf8(stdin);
	tcsetattr(STDIN_FILENO, TCSANOW, &oldattr);
	return ch;
}

char *history_readline(const char *prompt) { return history_readline_eol(prompt, '\0'); }

static void output(const char *fmt, const char *prompt, const char *line)
{
	size_t len = (strlen(line) * 10) + 1024;
	char *dstbuf = (char*)malloc(len);
	const char *src = line;
	char *dst = dstbuf;
	char last_ch = ' ';
	int i;

	while (*src && len) {
		if (key_words && (ispunct(last_ch) || isspace(last_ch))) {
			for (i = 0; key_words[i]; i++) {
				if (strncmp(src, key_words[i], strlen(key_words[i])))
					continue;

				char ch = src[strlen(key_words[i])];

				if (!ispunct(ch) && !isspace(ch))
					continue;

				size_t n = snprintf(dst, len, "%s%s%s", strcmp(key_words[i], "false") ? italic : red, key_words[i], normal);
				dst += n;
				len -= n;
				src += strlen(key_words[i]);
			}
		}

		last_ch = *src;
		*dst++ = *src++;
		len--;
	}

	*dst = '\0';
	printf(fmt, prompt, dstbuf);
	free(dstbuf);
}

void history_output(const char *prompt, const char *line) { output("%s%s\n", prompt, line); }

static int flash_check(int ch, char *line, char *dst, int quoted, int depth, int rhs, int lhs)
{
	const char *src = NULL;
	int i;

	if ((ch == rhs) && (src = strchr(line, lhs)) && (depth > 0) && !quoted) {
		for (i = 1; src && (i < depth); i++)
			src = strchr(src + 1, lhs);

		if (!src)
			return 0;

		printf("%s\e[%dD", SAVE, (int)substrlen_utf8(src, dst));
		fflush(stdout);
		msleep(300);
		printf("%s", UNSAVE);
		fflush(stdout);
		return 1;
	}

	return 0;
}

char *history_readline_eol(const char *prompt, char eol)
{
	static const char *save_prompt;
	static char tmp_prompt[1024*2];
	size_t block_size = 1024;
	char *line = (char*)malloc(block_size);
	char *dst = line;
	char escbuf[20], search[1024];
	char *escdst = escbuf;
	int escape = 0, is_insert = 0, reverse_search = 0;
	cmd *last = NULL;
	int tmp, i;

	printf("%s", prompt);
	fflush(stdout);
	int depth_paren = 0, depth_bracket = 0, depth_brace = 0, quoted = 0, quote = 0;

	while ((tmp = history_getch()) != EOF) {
		unsigned ch = (unsigned)tmp;

		// printf("%02X (%02X) ", tmp, (char)alt);

		if (!quoted && ((ch == '\'') || (ch == '"'))) {
			quoted = 1;
			quote = ch;
		}
		else if (quoted && (ch == quote))
			quoted = 0;

		if (!quoted) {
			if (ch == '(')
				depth_paren++;
			else if (ch == '[')
				depth_bracket++;
			else if (ch == '{')
				depth_brace++;
		}

		if (flash_check(ch, line, dst, quoted, depth_paren, ')', '('))
			;
		else if (flash_check(ch, line, dst, quoted, depth_bracket, ']', '['))
			;
		else if (flash_check(ch, line, dst, quoted, depth_brace, '}', '{'))
			;

		if (!quoted) {
			if (ch == ')')
				depth_paren--;
			else if (ch == ']')
				depth_bracket--;
			else if (ch == '}')
				depth_brace--;
		}

		if ((ch == 0x7f) || (ch == 0x08)) {
			if (dst != line) {
				int len = 0;
				char *src = dst;
				int remlen = strlen(src);

				do {
					dst--;
					len++;
				} while (is_char_utf8(dst));

				if (--len)
					putchar('\b');

				if (is_insert) {
					char *end = dst;

					while (remlen--)
						*end++ = *src++;

					*end = '\0';
					printf("\b\e[s%s\e[K\e[u", dst);
				}
				else {
					*dst = '\0';
					printf("\b\e[K");
				}

				fflush(stdout);
			}

			continue;
		}

		if (ch == '\e') {
			escdst = escbuf;
			escape = 1;
		}

		if (!escape && (ch == '\x04')) { // CTRL-D (kill)
			free(line);
			return NULL;
		}

		if (!escape && (ch == '\x0B')) { // CTRL-K (erase to end)
			int len = strlen(dst);

			for (i = 0; i < len; i++)
				putchar(' ');

			len = strlen_utf8(dst);

			for (i = 0; i < len; i++)
				putchar('\b');

			fflush(stdout);
			is_insert = 0;
			continue;
		}

		if (!escape && (ch == '\x01')) { // CTRL-A (start of line)
			int len = (int)(dst - line); // FIXME

			for (i = 0; i < len; i++)
				putchar('\b');

			fflush(stdout);
			dst = line;
			is_insert = 1;
			continue;
		}

		if (!escape && (ch == '\x05')) { // CTRL-E (end of line)
			int len = (int)strlen(dst);

			for (i = 0; i < len; i++)
				putchar(*dst++);

			fflush(stdout);
			dst = line + strlen(line);
			is_insert = 0;
			continue;
		}

		if (!escape && (ch == '\x10')) { // CTRL-P (PREV/UP)
			escape = 0;

			if (!g_history)
				continue;

			if (!last)
				last = g_history;
			else if (!last->next)
				continue;
			else
				last = last->next;

			free(line);
			line = (char*)malloc(strlen(last->line) + block_size);
			strcpy(line, last->line);
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			continue;
		}

		if (!escape && (ch == '\x0E')) { // CTRL-N (NEXT/DOWN)
			escape = 0;

			if (!g_history)
				continue;

			if (!last)
				last = g_history;
			else if (!last->prev)
				continue;
			else
				last = last->prev;

			free(line);
			line = (char*)malloc(strlen(last->line) + block_size);
			strcpy(line, last->line);
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			continue;
		}

		if (!escape && (ch == '\x12')) { // CTRL-R
			if (!g_history)
				continue;

			if (!reverse_search)
				save_prompt = prompt;

			prompt = "(reverse-search) \"\" : ";
			strcpy(tmp_prompt, prompt);
			output("\r%s%s", prompt, "");
			reverse_search = 1;
			search[0] = '\0';
			continue;
		}

		if (reverse_search) {
			if (ch == '\n') {
				prompt = save_prompt;
				reverse_search = 0;
				puts("\r");
				break;
			}

			if (!g_history)
				continue;

			char tmpbuf[2];
			tmpbuf[0] = ch;
			tmpbuf[1] = '\0';
			strcat(search, tmpbuf);
			snprintf(tmp_prompt, sizeof(tmp_prompt), "(reverse-search) \"%s\" : ", search);
			prompt = tmp_prompt;

			if (!last)
				last = g_history;
			else
				last = last->next;

			while (last) {
				if (strstr(last->line, search))
					break;

				last = last->next;
			}

			if (!last) {
				reverse_search = 0;
				continue;
			}

			free(line);
			line = strdup(last->line);
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			continue;
		}

		if (!escape) {
			char tmpbuf[20];
			put_char_utf8(tmpbuf, ch);
			printf("%s", tmpbuf);
			fflush(stdout);
		}

		if ((ch == '\n') && (line[strlen(line)-1] == eol))
			break;

		if (ch == '\n') {
			//*dst++ = '\n';
			printf(" |\t");
			fflush(stdout);
			continue;
		}

		if (!escape && is_insert) {
			int len = put_len_utf8(ch);
			int bytes = strlen(dst);
			char *src = line + strlen(line) - 1;
			char *end = line + strlen(line) + len - 1;
			end[1] = '\0';

			for (i = 0; i < bytes; i++)
				*end-- = *src--;

			printf("\e[s%s\e[u", dst + len);
			fflush(stdout);
		}

		if (escape) {
			if ((escdst - escbuf) < sizeof(escbuf)) {
				*escdst++ = ch;
				*escdst = '\0';
			}
		}
		else {
			dst += put_char_bare_utf8(dst, ch);
			size_t n = dst - line;

			if ((n + 5) > block_size) {
				line = (char*)realloc(line, block_size += 1024);
				dst = line + n;
			}

			if (!is_insert)
				*dst = '\0';
		}

		if (escape && !strcmp(escbuf, "\e[3~")) { // DELETE
			escape = 0;

			if (!is_insert)
				continue;

			if (dst == (line + strlen(line)))
				continue;

			for (i = 0; i < strlen(dst + 1); i++)
				dst[i] = dst[i + 1];

			dst[strlen(dst)-1] = '\0';
			printf("%s ", dst);

			for (i = 0; i < (strlen_utf8(dst) + 1); i++)
				putchar('\b');

			fflush(stdout);
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[H")) { // HOME
			escape = 0;

			while (dst != line) {
				int len = 0;

				do {
					dst--;
					len++;
				} while (is_char_utf8(dst));

				printf("\e[%dD", --len);
			}

			fflush(stdout);
			dst = line;
			is_insert = 1;
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[F")) { // END
			escape = 0;
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			is_insert = 0;
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[A")) { // UP
			escape = 0;

			if (!g_history)
				continue;

			if (!last)
				last = g_history;
			else if (!last->next)
				continue;
			else
				last = last->next;

			free(line);
			line = (char*)malloc(strlen(last->line) + block_size);
			strcpy(line, last->line);
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[B")) { // DOWN
			escape = 0;

			if (!g_history)
				continue;

			if (!last)
				last = g_history;
			else if (!last->prev)
				continue;
			else
				last = last->prev;

			free(line);
			line = (char*)malloc(strlen(last->line) + block_size);
			strcpy(line, last->line);
			output("\r%s%s\e[K", prompt, line);
			fflush(stdout);
			dst = line + strlen(line);
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[C")) { // RIGHT
			escape = 0;

			if (dst == (line + strlen(line))) {
				is_insert = 0;
				continue;
			}

			int len = 0;

			do {
				dst++;
				len++;
			} while (is_char_utf8(dst));

			printf("%s", escbuf);

			if (--len)
				printf("%s", escbuf);

			fflush(stdout);
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[D")) { // LEFT
			escape = 0;

			if (dst == line)
				continue;

			int len = 0;

			do {
				dst--;
				len++;
			} while (is_char_utf8(dst));

			printf("%s", escbuf);

			if (--len)
				printf("%s", escbuf);

			fflush(stdout);
			is_insert = 1;
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[1;5C")) { // CTRL-RIGHT
			escape = 0;

			if (dst == (line + strlen(line))) {
				is_insert = 0;
				continue;
			}

			int cnt = 0;

			while (*dst && !isalnum((*dst))) {
				dst++;
				cnt++;
			}

			while (*dst && isalnum((*dst))) {
				dst++;
				cnt++;
			}

			if (cnt) {
				printf("\e[%dC", cnt);
				fflush(stdout);
			}

			is_insert = 1;
			continue;
		}

		if (escape && !strcmp(escbuf, "\e[1;5D")) { // CTRL-LEFT
			escape = 0;

			if (dst == line)
				continue;

			int cnt = 0;

			while ((dst != line) && !isalnum(*(dst - 1))) {
				dst--;
				cnt++;
			}

			while ((dst != line) && !isalnum(*dst)) {
				dst--;
				cnt++;
			}

			while ((dst != line) && isalnum((*(dst - 1)))) {
				dst--;
				cnt++;
			}

			if (cnt) {
				printf("\e[%dD", cnt);
				fflush(stdout);
			}

			is_insert = 1;
			continue;
		}
	}

	if (g_last) {
		if (!strcmp(g_last, line))
			return line;
	}

	if (g_histfile) {
		fprintf(g_histfile, "%s\n", line);
		fflush(g_histfile);
	}

	cmd *n = (cmd *)malloc(sizeof(cmd));
	n->line = strdup(line);
	n->next = g_history;
	n->prev = NULL;

	if (g_history)
		g_history->prev = n;

	g_history = n;

	if (g_last)
		free(g_last);

	g_last = strdup(n->line);
	return line;
}

void history_keywords(const char **word_array) { key_words = word_array; }

void history_load(const char *filename)
{
	g_histfile = fopen(filename, "a+");

	if (!g_histfile)
		return;

	char line[1024 * 8]; // FIXME

	while (fgets(line, sizeof(line), g_histfile) != NULL) {
		line[strlen(line)-1] = '\0';
		cmd *n = (cmd *)malloc(sizeof(cmd));
		n->line = strdup(line);
		n->next = g_history;
		n->prev = NULL;

		if (g_history)
			g_history->prev = n;

		g_history = n;

		if (g_last)
			free(g_last);

		g_last = strdup(n->line);
	}
}

void history_save(void)
{
	while (g_history) {
		cmd *save = g_history;
		free(save->line);
		g_history = g_history->next;
		free(save);
	}

	if (g_histfile)
		fclose(g_histfile);

	if (g_last)
		free(g_last);

	g_histfile = NULL;
	g_history = NULL;
	g_last = NULL;
}
