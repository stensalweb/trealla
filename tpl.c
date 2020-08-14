#include <stdlib.h>
#include <time.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>

#ifdef _WIN32
#include <io.h>
#define snprintf _snprintf
#define isatty _isatty
#else
#include <unistd.h>
#endif

#include "history.h"
#include "parse.h"

#ifdef _WIN32
#include <windows.h>
#define msleep Sleep
#else
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#define msleep(ms)                                                                                                             \
	{                                                                                                                          \
		struct timespec tv;                                                                                                    \
		tv.tv_sec = (ms) / 1000;                                                                                               \
		tv.tv_nsec = ((ms) % 1000) * 1000 * 1000;                                                                              \
		nanosleep(&tv, &tv);                                                                                                   \
	}
#endif

static void sigfn(int s)
{
	signal(SIGINT, 0);
	g_tpl_abort = 1;
}

static int daemonize(int argc, char *argv[])
{
	char path[1024];
	path[0] = '\0';
	int watchdog = 0;

	for (int i = 0; i < argc; i++) {
		if (!strcmp(argv[i], "-w") || !strcmp(argv[i], "--watchdog"))
			watchdog = 1;
		else if (!strncmp(argv[i], "--cd=", 5))
			strcpy(path, argv[i] + 5);
	}

#ifdef _WIN32
	char cmd[1024], args[1024 * 8];
	args[0] = 0;
	strcpy(cmd, argv[0]);
	strcat(cmd, ".exe");

	for (int i = 0; i < argc; i++) {
		if (!strcmp(argv[i], "-d") || !strcmp(argv[i], "--daemon"))
			continue;

		if (!args[0])
			strcat(args, " ");

		strcat(args, "\"");
		strcat(args, argv[i]);
		strcat(args, "\"");
	}

	STARTUPINFO startInfo = {0};
	PROCESS_INFORMATION process = {0};

	startInfo.cb = sizeof(startInfo);
	startInfo.dwFlags = STARTF_USESHOWWINDOW;
	startInfo.wShowWindow = SW_HIDE;

	if (!CreateProcessA((LPSTR)cmd,              // application name
						(LPSTR)args,             // command line arguments
						NULL,                    // process attributes
						NULL,                    // thread attributes
						FALSE,                   // inherit (file) handles
						DETACHED_PROCESS,        // Detach
						NULL,                    // environment
						(path[0] ? path : NULL), // current directory
						&startInfo,              // startup info
						&process)                // process information
		) {
		fprintf(stdedrr, "Error: creation of the process failed\n");
		return 1;
	}

	return 0;
#else
	pid_t pid;

	if ((pid = fork()) < 0) // Error
		return -1;
	else if (pid != 0) // Parent
		return 0;

	if (watchdog)
		signal(SIGCHLD, SIG_IGN);

	while (watchdog) {
		pid_t pid;

		if ((pid = fork()) < 0) // Error
			return -1;
		else if (pid != 0) // Parent
		{
			if (watchdog) {
				int status;
				wait(&status);
				msleep(1000);
			}
			else
				return 0;
		}
		else // Child
			break;
	}

	if (path[0])
		if (chdir(path) < 0)
			fprintf(stderr, "Error: can't chdir(%s)\n", path);

	setsid();
	umask(0);
	close(2);
	close(1);
	close(0);
	return 1;
#endif
}

int main(int ac, char *av[])
{
	const char *homedir;

	if ((homedir = getenv("HOME")) == NULL)
		homedir = ".";

	char histfile[1024];
	snprintf(histfile, sizeof(histfile), "%s/%s", homedir, ".tpl_history");

	int i, do_load = 0, do_goal = 0, version = 0, quiet = 0, daemon = 0;
	void *pl = pl_create();
	set_opt(pl, 1);

	for (i = 1; i < ac; i++) {
		if (!strcmp(av[i], "--")) {
			g_ac = ac;
			g_avc = ++i;
			g_av = av;
			break;
		}

		if (!strcmp(av[i], "-h") || !strcmp(av[i], "--help")) {
			version = 2;
		}
		else if (!strcmp(av[i], "-v") || !strcmp(av[i], "--version")) {
			version = 1;
		}
		else if (!strcmp(av[i], "-q") || !strcmp(av[i], "--quiet")) {
			set_quiet(pl);
			quiet = 1;
		}
		else if (!strcmp(av[i], "-O0") || !strcmp(av[i], "--noopt"))
			set_opt(pl, 0);
		else if (!strcmp(av[i], "-t") || !strcmp(av[i], "--trace"))
			set_trace(pl);
		else if (!strcmp(av[i], "--stats"))
			set_stats(pl);
		else if (!strcmp(av[i], "--iso-only"))
			set_iso_only(pl);
		else if (!strcmp(av[i], "-d") || !strcmp(av[i], "--daemon"))
			daemon = 1;
	}

	if (daemon) {
		if (!daemonize(ac, av))
			return 0;
	} else
		signal(SIGINT, &sigfn);

	for (i = 1; i < ac; i++) {
		if (!strcmp(av[i], "--"))
			break;

		if (!strcmp(av[i], "--consult")) {
			if (!pl_consult_fp(pl, stdin)) {
				pl_destroy(pl);
				return 1;
			}
		}
		else if (!strcmp(av[i], "-l") || !strcmp(av[i], "--consult-file"))
			do_load = 1;
		else if (!strcmp(av[i], "-g") || !strcmp(av[i], "--query-goal"))
			do_goal = 1;
		else if (av[i][0] == '-')
			continue;
		else if (do_load) {
			do_load = 0;

			if (!pl_consult(pl, av[i])) {
				pl_destroy(pl);
				return 1;
			}
		}
		else if (do_goal) {
			do_goal = 0;

			if (!pl_eval(pl, av[i])) {
				pl_destroy(pl);
				return 1;
			}

			if (get_halt(pl)) {
				pl_destroy(pl);
				return 1;
			}
		}
	}

	if (!quiet)
		printf("Trealla ProLog (c) Infradig 2020, %s\n", VERSION);

	if ((version == 2) && !quiet) {
		fprintf(stderr, "Usage:\n");
		fprintf(stderr, "  tpl [options] [-l file] [-g goal]\n");
		fprintf(stderr, "Options:\n");
		fprintf(stderr, "  -v, --version\t\t- print version info and exit\n");
		fprintf(stderr, "  -h, --help\t\t- print help info and exit\n");
		fprintf(stderr, "  -O0, --noopt\t\t- turn off optimization\n");
		fprintf(stderr, "  -q, --quiet\t\t- quiet mode\n");
		fprintf(stderr, "  -t, --trace\t\t- trace mode\n");
		fprintf(stderr, "  -d, --daemon\t\t- daemonize\n");
		fprintf(stderr, "  -w, --watchdog\t\t- create watchdog\n");
		fprintf(stderr, "  --consult\t- consult from STDIN\n");
		fprintf(stderr, "  --stats\t\t- print stats\n");
		fprintf(stderr, "  --iso-only\t\t- ISO-only mode\n");
	}

	if (version && !quiet)
		return 0;

	if (isatty(0))
		history_load(histfile);

	char *line;

	while ((line = history_readline_eol("?- ", '.')) != NULL) {
		if (!strcmp(line, "halt.")) {
			free(line);
			break;
		}

		pl_eval(pl, line);
		free(line);

		if (get_halt(pl))
			break;

		if (isatty(0))
			history_output("", get_status(pl) ? "true." : "false.");
		else
			printf("%s\n", get_status(pl) ? "true" : "false");
	}

	if (isatty(0))
		history_save();

	int halt_code = get_halt_code(pl);
	pl_destroy(pl);
	return halt_code;
}
