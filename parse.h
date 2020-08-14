#pragma once

typedef struct prolog_ prolog;

prolog *pl_create();
void pl_destroy(prolog*);

int pl_eval(prolog*, const char *expr);
int pl_consult(prolog*, const char *filename);
int pl_consult_fp(prolog*, FILE *fp);

int get_halt_code(prolog*);
int get_halt(prolog*);
int get_status(prolog*);
void set_trace(prolog*);
void set_quiet(prolog*);
void set_stats(prolog*);
void set_iso_only(prolog*);
void set_opt(prolog*, int onoff);

extern int g_tpl_abort, g_ac, g_avc;
extern char **g_av;
