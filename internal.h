#pragma once

#include <stdint.h>
#include <stdio.h>
#include <limits.h>

#include "skiplist.h"

#ifndef USE_SSL
#define USE_SSL 0
#endif

#ifndef USE_INT128
#define USE_INT128 0
#endif

#if USE_INT128
typedef __int128_t int_t;
typedef __uint128_t uint_t;
#else
typedef __int64_t int_t;
typedef __uint64_t uint_t;
#endif

typedef uint32_t idx_t;

#define MAX_VAR_POOL_SIZE 1000
#define MAX_ARITY UCHAR_MAX
#define MAX_SMALL_STRING (sizeof(int_t)*2)
#define MAX_USER_OPS 100
#define MAX_QUEUES 16
#define MAX_STREAMS 64
#define STREAM_BUFLEN 1024

#define GET_STR(c) ((c)->val_type != TYPE_STRING ? g_pool+((c)->val_offset) : (c)->flags&FLAG_SMALL_STRING ? (c)->val_chars : (c)->val_str)
#define LEN_STR(c) ((c->flags&FLAG_BINARY) ? c->nbytes : strlen(GET_STR(c)))

#define GET_FRAME(i) q->frames+(i)
#define GET_SLOT(g,i) (i) < g->nbr_slots ? q->slots+g->env+(i) : q->slots+g->overflow+((i)-g->nbr_slots)

#define GET_VALUE(q,c,c_ctx) !is_var(c) ? (q->latest_ctx = c_ctx, c) : deref_var(q, c, c_ctx)

#define is_var(c) ((c)->val_type == TYPE_VAR)
#define is_literal(c) ((c)->val_type == TYPE_LITERAL)
#define is_string(c) ((c)->val_type == TYPE_STRING)
#define is_indirect(c) ((c)->val_type == TYPE_INDIRECT)
#define is_integer(c) (((c)->val_type == TYPE_INT) && ((c)->val_den == 1))
#define is_rational(c) ((c)->val_type == TYPE_INT)
#define is_real(c) ((c)->val_type == TYPE_FLOAT)
#define is_empty(c) ((c)->val_type == TYPE_EMPTY)
#define is_end(c) ((c)->val_type == TYPE_END)

#define is_number(c) (is_rational(c) || is_real(c))
#define is_atom(c) ((is_literal(c) && !(c)->arity) || is_string(c))
#define is_structure(c) (is_literal(c) && (c)->arity)
#define is_list(c) (is_literal(c) && ((c)->arity == 2) && ((c)->val_offset == g_dot_s))
#define is_nil(c) (is_literal(c) && !(c)->arity && ((c)->val_offset == g_nil_s))
#define is_smallstring(c) ((c)->flags&FLAG_SMALL_STRING)
#define is_bigstring(c) (is_string(c) && !is_smallstring(c))
#define is_const(c) (is_string(c) && ((c)->flags&FLAG_CONST))

enum {
	TYPE_EMPTY=0,
	TYPE_VAR,
	TYPE_LITERAL,
	TYPE_STRING,
	TYPE_INT,
	TYPE_FLOAT,
	TYPE_INDIRECT,
	TYPE_END
};

enum {
	FLAG_BUILTIN=1<<0,
	FLAG_HEX=1<<1,						// only used with TYPE_INT
	FLAG_OCTAL=1<<2,					// only used with TYPE_INT
	FLAG_BINARY=1<<3,					// only used with TYPE_INT
	FLAG_TAIL=1<<4,
	FLAG_TAILREC=1<<5,
	FLAG_SMALL_STRING=1<<6,
	FLAG_PASSTHRU=1<<7,

	//FLAG_SPARE1=1<<8,

	FLAG_RETURN=FLAG_HEX,				// only used with TYPE_END
	FLAG_FIRST_USE=FLAG_HEX,			// only used with TYPE_VAR
	FLAG_SLICE=FLAG_HEX,			    // only used with TYPE_STRING
	FLAG_CONST=FLAG_OCTAL,			    // only used with TYPE_STRING
	FLAG_STREAM=FLAG_SMALL_STRING,		// only used with TYPE_INT
	FLAG_DELETED=FLAG_HEX,				// only used by bagof

	OP_FX=1<<9,
	OP_FY=1<<10,
	OP_XF=1<<11,
	OP_YF=1<<12,
	OP_YFX=1<<13,
	OP_XFX=1<<14,
	OP_XFY=1<<15
};

typedef struct module_ module;
typedef struct query_ query;
typedef struct rule_ rule;
typedef struct clause_ clause;
typedef struct cell_ cell;
typedef struct parser_ parser;

struct cell_ {
	struct {
		uint8_t val_type;
		uint8_t arity;
		uint16_t flags;
		idx_t nbr_cells;
	};

	union {
		struct {
			union {
				rule *match;				// rules
				int (*fn)(query*);			// builtins
				size_t nbytes;              // slice size
				uint16_t precedence;		// ops parsing
				uint8_t slot_nbr;			// vars
				int_t val_den;				// rational denominator
			};

			union {
				int_t val_int;				// integer
				int_t val_num;				// rational numerator
				double val_real;			// float
				unsigned val_offset;		// offset to string in pool
				char *val_str;				// C-string
				cell *val_cell;				// indirect
			};
		};

		char val_chars[MAX_SMALL_STRING];	// small string copy
	};
};

typedef struct {
	idx_t nbr_cells, cidx;
	uint8_t nbr_vars, first_cut, cut_only, deleted, persist;
	cell cells[];
} term;

typedef struct {
	uint64_t u1, u2;
} uuid;

struct clause_ {
	clause *next;
	module *m;
	uuid u;
	term t;
};

enum {
	FLAG_RULE_PREBUILT=1<<0,
	FLAG_RULE_DYNAMIC=1<<1,
	FLAG_RULE_PUBLIC=1<<2,
	FLAG_RULE_VOLATILE=1<<3,
	FLAG_RULE_PERSIST=1<<4
};

struct rule_ {
	rule *next;
	clause *head, *tail;
	skiplist *index;
	idx_t val_offset;
	uint8_t arity, flags;
};

struct builtins {
	const char *name;
	unsigned arity;
	int (*fn)(query*);
	const char *help;
};

struct op_table {
	const char *name;
	unsigned val_type;
	unsigned precedence;
};

typedef struct {
	idx_t ctx;
	uint8_t slot_nbr;
} trail;

typedef struct {
	cell c;
	idx_t ctx;
} slot;

typedef struct {
	cell *curr_cell;
	idx_t prev_frame, env, overflow;
	uint8_t any_choices, nbr_vars, nbr_slots;
} frame;

typedef struct {
	FILE *fp;
	char *mode, *filename, *name, *data, *src;
	void *sslptr;
	parser *p;
	char srcbuf[STREAM_BUFLEN];
	size_t data_len, alloc_nbytes;
	int ungetch, srclen;
	uint8_t did_getc, nodelay, nonblock, udp, ssl;
} stream;

typedef struct {
	cell *curr_cell;
	clause *curr_clause;
	sliter *iter;
	idx_t curr_frame, fp, hp, tp, sp, anbr;
} qstate;

typedef struct {
	qstate st;
	uint32_t pins;
	idx_t v1, v2;
	uint8_t nbr_vars, inner_cut, any_choices, catchme, qnbr;
} choice;

typedef struct arena_ arena;

struct arena_ {
	arena *next;
	cell *heap;
	idx_t hp, h_size;
	unsigned nbr;
};

struct query_ {
	query *prev, *next, *parent;
	module *m;
	frame *frames;
	slot *slots;
	choice *choices;
	trail *trails;
	cell *last_arg, *tmpq[MAX_QUEUES], *exception;
	cell *tmp_heap, *queue[MAX_QUEUES];
	arena *arenas;
	cell accum;
	qstate st;
	int64_t time_started, tmo;
	uint64_t tot_goals, tot_retries, tot_matches, tot_tcos, step, qid;
	uint64_t nv_mask;
	int halt, halt_code, status, error, trace, calc, qnbr, yielded;
	int retry, resume, no_tco, current_input, current_output;
	int max_depth, quoted, nl, fullstop, ignore_ops, character_escapes;
	int is_subquery;
	idx_t cp, tmphp, nv_start;
	idx_t latest_ctx, popp, qp[MAX_QUEUES];
	idx_t nbr_frames, nbr_slots, nbr_trails, nbr_choices;
	idx_t max_choices, max_frames, max_slots, max_trails, max_heaps;
	idx_t tot_heaps, tot_heapsize, tmpq_size[MAX_QUEUES];
	idx_t h_size, tmph_size, q_size[MAX_QUEUES], anbr;
};

struct parser_ {
	struct {
		char var_pool[MAX_VAR_POOL_SIZE];
		unsigned var_used[MAX_ARITY];
		const char *var_name[MAX_ARITY];
	} vartab;

	FILE *fp;
	module *m;
	term *t;
	char *token, *save_line, *srcptr;
	size_t token_size, n_line;
	int start_term, end_of_term, line_nbr, comment, error;
	int directive, consulting, one_shot, dq_consing, depth;
	int quoted, is_var, is_op, skip, command, in_dcg, dcg_passthru;
	unsigned val_type;
};

struct module_ {
	module *next;
	query *tasks;
	char *name, *filename;
	rule *head, *tail;
	parser *p;
	FILE *fp;
	struct op_table ops[MAX_USER_OPS+1];
    const char *keywords[1000];

	struct {
		int double_quote_codes, double_quote_chars, double_quote_atom;
		int character_escapes;
		int rational_syntax_natural, prefer_rationals;
	} flag;

	int prebuilt, dq, halt, halt_code, status, trace, quiet, dirty;
	int user_ops, opt, stats, iso_only, use_persist, loading;
};

extern idx_t g_empty_s, g_dot_s, g_cut_s, g_nil_s, g_true_s, g_fail_s;
extern idx_t g_anon_s, g_clause_s, g_eof_s, g_lt_s;
extern idx_t g_gt_s, g_eq_s, g_sys_elapsed_s, g_sys_queue_s;
extern stream g_streams[MAX_STREAMS];
extern module *g_modules;
extern char *g_pool;

#define copy_cells(dst,src,nbr_cells) memcpy(dst, src, sizeof(cell)*(nbr_cells))

int is_in_pool(const char *name, idx_t *offset);
cell *deref_var(query *q, cell *c, idx_t ctx);
void set_var(query *q, cell *c, idx_t ctx, cell *v, idx_t v_ctx);
void reset_value(query *q, cell *c, idx_t c_ctx, cell *v, idx_t v_ctx);
int unify(query *q, cell *p1, idx_t p1_ctx, cell *p2, idx_t p2_ctx);
int module_load_fp(module *m, FILE *fp);
int module_load_file(module *m, const char *filename);
int module_save_file(module *m, const char *filename);
int deconsult(const char *filename);
module *create_module(const char *name);
void destroy_module(module *m);
module *find_module(const char *name);
int abolish_from_db(module *m, cell *c);
clause *asserta_to_db(module *m, term *t, int consulting);
clause *assertz_to_db(module *m, term *t, int consulting);
void retract_from_db(module *m, clause *r);
int erase_from_db(module *m, uuid *ref);
clause *find_in_db(module *m, uuid *ref);
int get_op(module *m, const char *name, unsigned *val_type, int *userop, int hint_prefix);
void write_canonical(query *q, FILE *fp, cell *c, int running, int dq, int depth);
size_t write_canonical_to_buf(query *q, char *dst, size_t dstlen, cell *c, int running, int dq, int depth);
void write_term(query *q, FILE *fp, cell *c, int running, int dq, int cons, int max_depth, int depth);
size_t write_term_to_buf(query *q, char *dst, size_t dstlen, cell *c, int running, int dq, int cons, int max_depth, int depth);
void make_choice(query *q);
void cut_me(query *q, int inner_cut);
int check_builtin(module *m, const char *name, unsigned arity);
void *get_builtin(module *m, const char *name, unsigned arity);
void query_execute(query *q, term *t);
cell *get_head(module *m, cell *c);
cell *get_body(module *m, cell *c);
rule *find_match(module *m, cell *c);
rule *find_functor(module *m, const char *name, unsigned arity);
int call_me(query *q, cell *p1, idx_t p1_ctx);
void undo_me(query *q);
parser *create_parser(module *m);
void destroy_parser(parser *p);
int parser_tokenize(parser *p, int args, int consing);
int parser_attach(parser *p, int start_idx);
int parser_xref(parser *p, term *t, rule *parent);
idx_t drop_choice(query *q);
int retry_choice(query *q);
void parser_assign_vars(parser *p);
query *create_query(module *m, int sub_query);
query *create_subquery(query *q, cell *curr_cell);
void destroy_query(query *q);
void run_query(query *q);
cell *deep_clone_term_on_heap(query *q, cell *p1, idx_t p1_ctx);
cell *clone_term(query *q, int prefix, cell *p1, idx_t p1_ctx, idx_t suffix);
void make_end(cell *tmp);
int do_match(query *q, cell *curr_cell);
idx_t find_in_pool(const char *name);
void do_reduce(cell *n);
unsigned create_vars(query *q, unsigned nbr);
unsigned count_bits(uint64_t mask, unsigned bit);
void try_me(const query *q, unsigned vars);
void load_keywords(module *m);
void throw_error(query *q, cell *c, const char *err_type, const char *expected);
char *uuid_to_string(const uuid *u, char *buf, size_t buflen);
int uuid_from_string(const char *s, uuid *u);
void uuid_gen(uuid *u);
uint64_t gettimeofday_usec(void);
void clear_term(term *t);
