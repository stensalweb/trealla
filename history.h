#ifndef HISTORY_H
#define HISTORY_H

extern void history_load(const char *filename);
extern void history_keywords(const char **word_array);
extern char *history_readline(const char *prompt);
extern char *history_readline_eol(const char *prompt, char eol);
extern void history_output(const char *prompt, const char *line);
extern void history_save(void);

extern int history_getch(void);

#endif
