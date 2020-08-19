#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <ctype.h>
#include <float.h>
#include <sys/time.h>

#ifdef _WIN32
#include <io.h>
#define isatty _isatty
#else
#include <unistd.h>
#endif

#include "internal.h"
#include "history.h"
#include "library.h"
#include "parse.h"
#include "utf8.h"

static const unsigned INITIAL_TOKEN_SIZE = 100;
static const unsigned INITIAL_POOL_SIZE = 4000;
static const unsigned INITIAL_NBR_CELLS = 100;
static const unsigned INITIAL_NBR_HEAP = 8000;
static const unsigned INITIAL_NBR_QUEUE = 1000;

static const unsigned INITIAL_NBR_GOALS = 1000;
static const unsigned INITIAL_NBR_SLOTS = 1000;
static const unsigned INITIAL_NBR_CHOICES = 1000;
static const unsigned INITIAL_NBR_TRAILS = 1000;

struct prolog_ {
	module *m;
};

stream g_streams[MAX_STREAMS] = {{0}};
char *g_pool = NULL;
idx_t g_empty_s, g_dot_s, g_cut_s, g_nil_s, g_true_s, g_fail_s;
idx_t g_anon_s, g_clause_s, g_eof_s, g_lt_s, g_gt_s, g_eq_s;
idx_t g_sys_elapsed_s, g_sys_queue_s;

static idx_t g_pool_offset = 0, g_pool_size = 0;
static int g_tpl_count = 0;

int g_ac = 0, g_avc = 1;
char **g_av = NULL;

static struct op_table g_ops[] =
{
	{":-", OP_XFX, 1200},
	{":-", OP_FX, 1200},
	{"-->", OP_XFX, 1200},
	{"?-", OP_FX, 1200},
	{";", OP_XFY, 1100},
	{"|", OP_XFY, 1100},
	{"->", OP_XFY, 1050},
	{"*->", OP_XFY, 1050},
	{",", OP_XFY, 1000},

	{"op", OP_FX, 1150},
	{"dynamic", OP_FX, 1150},
	{"volatile", OP_FX, 1150},
	{"initialization", OP_FX, 1150},
	{"set_prolog_flag", OP_FX, 1150},
	{"module", OP_FX, 1150},
	{"use_module", OP_FX, 1150},
	{"public", OP_FX, 1150},
	{"export", OP_FX, 1150},
	{"import", OP_FX, 1150},

	{"\\+", OP_FY, 900},
	{"is", OP_XFX, 700},
	{"=", OP_XFX, 700},
	{"\\=", OP_XFX, 700},
	{"==", OP_XFX, 700},
	{"\\==", OP_XFX, 700},
	{"=:=", OP_XFX, 700},
	{"=\\=", OP_XFX, 700},
	{"<", OP_XFX, 700},
	{"=<", OP_XFX, 700},
	{">", OP_XFX, 700},
	{">=", OP_XFX, 700},
	{"@<", OP_XFX, 700},
	{"@=<", OP_XFX, 700},
	{"@>", OP_XFX, 700},
	{"@>=", OP_XFX, 700},
	{"=..", OP_XFX, 700},
	{":", OP_XFY, 600},
	{"+", OP_YFX, 500},
	{"-", OP_YFX, 500},
	{"?", OP_FX, 500},

    {"rdiv", OP_YFX, 400},

	{"*", OP_YFX, 400},
	{"/", OP_YFX, 400},
	{"//", OP_YFX, 400},
	{"div", OP_YFX, 400},
	{"rdiv", OP_YFX, 400},
	{"\\/", OP_YFX, 400},
	{"/\\", OP_YFX, 400},
	{"rem", OP_YFX, 400},
	{"mod", OP_YFX, 400},
	{"xor", OP_YFX, 400},
	{"and", OP_YFX, 400},
	{"or", OP_YFX, 400},
	{"<<", OP_YFX, 400},
	{">>", OP_YFX, 400},
	{"**", OP_XFX, 200},
	{"^", OP_XFY, 200},
	{"\\", OP_FY, 200},
	{"-", OP_FY, 200},
	{"+", OP_FY, 200},

	//{"$", OP_FX, 1},

	{0}
};

int is_in_pool(const char *name, idx_t *val)
{
	idx_t offset = 0;

	while (offset < g_pool_offset) {
		if (!strcmp(g_pool+offset, name)) {
			if (val)
				*val = offset;

			return 1;
		}

		offset += strlen(g_pool+offset) + 1;
	}

	return 0;
}

idx_t find_in_pool(const char *name)
{
	idx_t offset;

	if (is_in_pool(name, &offset))
		return offset;

	offset = g_pool_offset;
	size_t len = strlen(name);

	if ((offset+len+1) >= g_pool_size) {
		g_pool = realloc(g_pool, g_pool_size*=2);
		if (!g_pool) abort();
	}

	strcpy(g_pool+offset, name);
	g_pool_offset += len + 1;
	return offset;
}

int get_op(module *m, const char *name, unsigned *val_type, int *userop, int hint_prefix)
{
	for (const struct op_table *ptr = m->ops; ptr->name; ptr++) {
		if (hint_prefix && (ptr->val_type != OP_FX) && (ptr->val_type != OP_FY))
			continue;

		if (!strcmp(ptr->name, name)) {
			if (val_type) *val_type = ptr->val_type;
			if (userop) *userop = 1;
			return ptr->precedence;
		}
	}

	for (const struct op_table *ptr = g_ops; ptr->name; ptr++) {
		if (hint_prefix && (ptr->val_type != OP_FX) && (ptr->val_type != OP_FY))
			continue;

		if (!strcmp(ptr->name, name)) {
			if (val_type) *val_type = ptr->val_type;
			if (userop) *userop = 0;
			return ptr->precedence;
		}
	}

	if (hint_prefix)
		return get_op(m, name, val_type, userop, 0);

	return 0;
}

static int set_op(module *m, const char *name, unsigned val_type, unsigned precedence)
{
	struct op_table *ptr = m->ops;
	name = g_pool + find_in_pool(name);

	for (; ptr->name; ptr++) {
		if (!strcmp(ptr->name, name)) {
			ptr->name = name;
			ptr->val_type = val_type;
			ptr->precedence = precedence;
			return 1;
		}
	}

	if (!m->user_ops)
		return 0;

	m->user_ops--;
	ptr->name = name;
	ptr->val_type = val_type;
	ptr->precedence = precedence;
	return 1;
}

module *g_modules = NULL;

module *find_module(const char *name)
{
	for (module *m = g_modules; m; m = m->next) {
		if (!strcmp(m->name, name))
			return m;
	}

	return NULL;
}

cell *get_head(module *m, cell *c)
{
	if (!is_literal(c))
		return NULL;

	if (c->val_offset != g_clause_s)
		return c;

	return c + 1;
}

cell *get_body(module *m, cell *c)
{
	if (!is_literal(c))
		return NULL;

	if (c->val_offset != g_clause_s)
		return NULL;

	c = c + 1;
	c += c->nbr_cells;

	if (is_end(c))
		return NULL;

	return c;
}

rule *find_match(module *m, cell *c)
{
	for (rule *h = m->head; h; h = h->next) {
		if ((h->val_offset == c->val_offset) && (h->arity == c->arity))
			return h;
	}

	return NULL;
}

rule *find_functor(module *m, const char *name, unsigned arity)
{
	for (rule *h = m->head; h; h = h->next) {
		if (!strcmp(g_pool+h->val_offset, name) && (h->arity == arity))
			return h;
	}

	return NULL;
}

uint64_t gettimeofday_usec(void)
#ifdef _WIN32
{
    static const uint64_t epoch = 116444736000000000ULL;
    FILETIME file_time;
    SYSTEMTIME system_time;
    ULARGE_INTEGER u;
    GetSystemTime(&system_time);
    SystemTimeToFileTime(&system_time, &file_time);
    u.LowPart = file_time.dwLowDateTime;
    u.HighPart = file_time.dwHighDateTime;
    return (u.QuadPart - epoch) / 10 + (1000ULL * system_time.wMilliseconds);
}
#else
{
    struct timeval tp;
    gettimeofday(&tp, NULL);
    return ((uint64_t)tp.tv_sec * 1000 * 1000) + tp.tv_usec;
}
#endif

static void compare_and_zero(uint64_t v1, uint64_t *v2, uint64_t *v)
{
	if (v1 != *v2) {
		*v2 = v1;
		*v = 0;
	}
}

#define MASK_FINAL 0x0000FFFFFFFFFFFF // Final 48 bits

void uuid_gen(uuid *u)
{
	static uint64_t s_last = 0, s_cnt = 0;
	static uint64_t g_seed = 0;

	if (!g_seed)
		g_seed = (uint64_t)time(0) & MASK_FINAL;

	uint64_t now = gettimeofday_usec();
	compare_and_zero(now, &s_last, &s_cnt);
	u->u1 = now;
	u->u2 = s_cnt++;
	u->u2 <<= 48;
	u->u2 |= g_seed;
}

char *uuid_to_string(const uuid *u, char *buf, size_t buflen)
{
	snprintf(buf, buflen, "%016llX-%04llX-%012llX",
		(unsigned long long)u->u1,
		(unsigned long long)(u->u2 >> 48),
		(unsigned long long)(u->u2 & MASK_FINAL));

	return buf;
}

int uuid_from_string(const char *s, uuid *u)
{
	if (!s) {
		uuid tmp = {0};
		*u = tmp;
		return 0;
	}

	unsigned long long p1 = 0, p2 = 0, p3 = 0;

	if (sscanf(s, "%llX%*c%llX%*c%llX", &p1, &p2, &p3) != 3) {
		uuid tmp = {0};
		*u = tmp;
		return 0;
	}

	u->u1 = p1;
	u->u2 = p2 << 48;
	u->u2 |= p3 & MASK_FINAL;
	return 1;
}

static rule *create_rule(module *m, cell *c)
{
	rule *h = calloc(1, sizeof(rule));

	if (m->tail)
		m->tail->next = h;

	m->tail = h;

	if (!m->head)
		m->head = h;

	h->val_offset = c->val_offset;
	h->arity = c->arity;
	return h;
}

static int compkey(const void *ptr1, const void *ptr2)
{
	const cell *p1 = (const cell*)ptr1;
	const cell *p2 = (const cell*)ptr2;

	if (is_integer(p1)) {
		if (is_integer(p2)) {
			if (p1->val_int < p2->val_int)
				return -1;
			else if (p1->val_int > p2->val_int)
				return 1;
			else
				return 0;
		} else if (is_var(p2))
			return 0;
	} else if (is_real(p1)) {
		if (is_real(p2)) {
			if (p1->val_real < p2->val_real)
				return -1;
			else if (p1->val_real > p2->val_real)
				return 1;
			else
				return 0;
		} else if (is_var(p2))
			return 0;
	} else if (is_atom(p1)) {
		if (is_atom(p2))
			return strcmp(GET_STR(p1), GET_STR(p2));
		else if (is_var(p2))
			return 0;
	} else if (is_var(p1)) {
		return 0;
	} else if (is_structure(p1)) {
		if (is_structure(p2)) {
			if (p1->arity < p2->arity)
				return -1;

			if (p1->arity > p2->arity)
				return 1;

			int i = strcmp(GET_STR(p1), GET_STR(p2));

			if (i != 0)
				return i;

			int arity = p1->arity;
			p1++; p2++;

			while (arity--) {
				int i = compkey(p1, p2);

				if (i != 0)
					return i;

				p1 += p1->nbr_cells;
				p2 += p2->nbr_cells;
			}

			return 0;
		} else if (is_var(p2))
			return 0;
	} else
		return 0;

	return 0;
}

enum log_type { LOG_ASSERTA=1, LOG_ASSERTZ=2, LOG_ERASE=3 };

static void db_log(module *m, clause *r, enum log_type l)
{
}

clause *asserta_to_db(module *m, term *t, int consulting)
{
	cell *c = get_head(m, t->cells);

	if (!c) {
		fprintf(stderr, "Error: not a fact or clause\n");
		return NULL;
	}

	rule *h = find_match(m, c);

	if (h && !consulting) {
		if (!(h->flags&FLAG_RULE_DYNAMIC)) {
			fprintf(stderr, "Error: not a fact or clause\n");
			return NULL;
		}
	}

	if (!h) {
		h = create_rule(m, c);

		if (!consulting) {
			h->flags |= FLAG_RULE_DYNAMIC;
			h->index = sl_create(compkey);
		}
	}


	if (m->prebuilt)
		h->flags |= FLAG_RULE_PREBUILT;

	int nbr_cells = t->cidx;
	clause *r = calloc(sizeof(clause)+(sizeof(cell)*nbr_cells), 1);
	memcpy(&r->t, t, sizeof(term));
	copy_cells(r->t.cells, t->cells, nbr_cells);
	r->t.nbr_cells = nbr_cells;
	r->m = m;
	r->next = h->head;
	h->head = r;

	if (!h->tail)
		h->tail = r;

	if ((h->flags&FLAG_RULE_DYNAMIC) && (c->arity > 0)) {
		cell *c = get_head(m, r->t.cells);
		sl_set(h->index, c, r);
	}

	t->cidx = 0;
	uuid_gen(&r->u);

	if (!m->loading && (h->flags&FLAG_RULE_PERSIST))
		db_log(m, r, LOG_ASSERTA);

	if (h->flags&FLAG_RULE_PERSIST)
		r->t.persist = 1;

	return r;
}

clause *assertz_to_db(module *m, term *t, int consulting)
{
	cell *c = get_head(m, t->cells);

	if (!c) {
		fprintf(stderr, "Error: no fact or clause head\n");
		return NULL;
	}

	rule *h = find_match(m, c);

	if (h && !consulting) {
		if (!(h->flags&FLAG_RULE_DYNAMIC)) {
			fprintf(stderr, "Error: not a fact or clause\n");
			return NULL;
		}
	}

	if (!h) {
		h = create_rule(m, c);

		if (!consulting) {
			h->flags |= FLAG_RULE_DYNAMIC;
			h->index = sl_create(compkey);
		}
	}

	if (m->prebuilt)
		h->flags |= FLAG_RULE_PREBUILT;

	int nbr_cells = t->cidx;
	clause *r = calloc(sizeof(clause)+(sizeof(cell)*nbr_cells), 1);
	memcpy(&r->t, t, sizeof(term));
	copy_cells(r->t.cells, t->cells, nbr_cells);
	r->t.nbr_cells = nbr_cells;
	r->m = m;

	if (h->tail)
		h->tail->next = r;

	h->tail = r;

	if (!h->head)
		h->head = r;

	if ((h->flags&FLAG_RULE_DYNAMIC) && (c->arity > 0)) {
		cell *c = get_head(m, r->t.cells);
		sl_app(h->index, c, r);
	}

	t->cidx = 0;
	uuid_gen(&r->u);

	if (!m->loading && (h->flags&FLAG_RULE_PERSIST))
		db_log(m, r, LOG_ASSERTZ);

	if (h->flags&FLAG_RULE_PERSIST)
		r->t.persist = 1;

	return r;
}

void retract_from_db(module *m, clause *r)
{
	r->t.deleted = 1;
	m->dirty = 1;

	if (!m->loading && r->t.persist)
		db_log(m, r, LOG_ERASE);
}

int abolish_from_db(module *m, cell *c)
{
	rule *h = find_match(m, c);

	if (h) {
		if (!(h->flags&FLAG_RULE_DYNAMIC)) {
			fprintf(stderr, "Error: not dynamic '%s/%u'\n", GET_STR(c), c->arity);
			return 0;
		}

		for (clause *r = h->head ; r; r = r->next)
			retract_from_db(m, r);

		h->flags = 0;
	}

	return 1;
}

clause *find_in_db(module *m, uuid *ref)
{
	for (rule *h = m->head; h; h = h->next) {
		for (clause *r = h->head ; r; r = r->next) {
			if (!memcmp(&r->u, ref, sizeof(uuid)))
				return r;
		}
	}

	return NULL;
}

int erase_from_db(module *m, uuid *ref)
{
	clause *r = find_in_db(m, ref);

	if (!r)
		return 0;

	r->t.deleted = 1;

	if (!m->loading && r->t.persist)
		db_log(m, r, LOG_ERASE);

	return 1;
}

static void set_dynamic_in_db(module *m, const char *name, idx_t arity)
{
	cell tmp;
	tmp.val_type = TYPE_LITERAL;
	tmp.val_offset = find_in_pool(name);
	tmp.arity = arity;
	rule *h = find_match(m, &tmp);
	if (!h) h = create_rule(m, &tmp);
	h->flags |= FLAG_RULE_DYNAMIC;
	h->index = sl_create(compkey);
}

static void set_persist_in_db(module *m, const char *name, idx_t arity)
{
	cell tmp;
	tmp.val_type = TYPE_LITERAL;
	tmp.val_offset = find_in_pool(name);
	tmp.arity = arity;
	rule *h = find_match(m, &tmp);
	if (!h) h = create_rule(m, &tmp);
	h->flags |= FLAG_RULE_DYNAMIC | FLAG_RULE_PERSIST;
	h->index = sl_create(compkey);
	m->use_persist = 1;
}

static void set_volatile_in_db(module *m, const char *name, unsigned arity)
{
	cell tmp;
	tmp.val_type = TYPE_LITERAL;
	tmp.val_offset = find_in_pool(name);
	tmp.arity = arity;
	rule *h = find_match(m, &tmp);
	if (!h) return;
	h->flags |= FLAG_RULE_VOLATILE;
}

void clear_term(term *t)
{
	for (idx_t i = 0; i < t->cidx; i++) {
		cell *c = t->cells + i;

		if (is_bigstring(c) && !is_const(c))
			free(c->val_str);

		c->val_type = TYPE_EMPTY;
	}

	t->cidx = 0;
}

static cell *make_cell(parser *p)
{
	while (p->t->cidx >= p->t->nbr_cells) {
		int nbr_cells = p->t->nbr_cells * 2;
		p->t = realloc(p->t, sizeof(term)+(sizeof(cell)*nbr_cells));
		if (!p->t) abort();
		p->t->nbr_cells = nbr_cells;
	}

	return p->t->cells + p->t->cidx++;
}

parser *create_parser(module *m)
{
	parser *p = calloc(1, sizeof(parser));
	p->token = calloc(p->token_size=INITIAL_TOKEN_SIZE+1, 1);
	idx_t nbr_cells = INITIAL_NBR_CELLS;
	p->t = calloc(sizeof(term)+(sizeof(cell)*nbr_cells), 1);
	p->t->nbr_cells = nbr_cells;
	p->start_term = 1;
	p->line_nbr = 1;
	p->m = m;
	return p;
}

void destroy_parser(parser *p)
{
	clear_term(p->t);
	free(p->token);
	free(p->t);
	free(p);
}

query *create_query(module *m, int small)
{
	static uint64_t g_subq_id = 0;

	query *q = calloc(1, sizeof(query));
	q->qid = g_subq_id++;
	q->m = m;
	q->trace = m->trace;
	q->nbr_frames = small ? INITIAL_NBR_GOALS/10 : INITIAL_NBR_GOALS;
	q->nbr_slots = small ? INITIAL_NBR_SLOTS/10 : INITIAL_NBR_SLOTS;
	q->nbr_choices = small ? INITIAL_NBR_CHOICES/10 : INITIAL_NBR_CHOICES;
	q->nbr_trails = small ? INITIAL_NBR_TRAILS/10 : INITIAL_NBR_TRAILS;
	q->frames = calloc(q->nbr_frames, sizeof(frame));
	q->slots = calloc(q->nbr_slots, sizeof(slot));
	q->choices = calloc(q->nbr_choices, sizeof(choice));
	q->trails = calloc(q->nbr_trails, sizeof(trail));
	q->h_size = small ? INITIAL_NBR_HEAP/10 : INITIAL_NBR_HEAP;
	q->tmph_size = small ? INITIAL_NBR_CELLS/10 : INITIAL_NBR_CELLS;
	q->current_input = 0;
	q->current_output = 1;
	q->accum.val_den = 1;

	for (int i = 0; i < MAX_QUEUES; i++)
		q->q_size[i] = small ? INITIAL_NBR_QUEUE/10 : INITIAL_NBR_QUEUE;

	return q;
}

query *create_subquery(query *q, cell *curr_cell)
{
	query *subq = create_query(q->m, 1);
	subq->parent = q;
	subq->st.fp = 1;
	subq->is_subquery = 1;
	subq->current_input = q->current_input;
	subq->current_output = q->current_output;

	cell *tmp = clone_term(subq, 0, curr_cell, 0, 1);
	idx_t nbr_cells = tmp->nbr_cells;
	make_end(tmp+nbr_cells);
	subq->st.curr_cell = tmp;

	frame *gsrc = GET_FRAME(q->st.curr_frame);
	frame *gdst = subq->frames;
	gdst->nbr_vars = gsrc->nbr_vars;
	slot *e = GET_SLOT(gsrc, 0);

	for (unsigned i = 0; i < gsrc->nbr_vars; i++, e++) {
		cell *c = GET_VALUE(q, &e->c, e->ctx);
		cell tmp;
		tmp.val_type = TYPE_VAR;
		tmp.slot_nbr = i;
		set_var(subq, &tmp, 0, c, q->latest_ctx);
	}

	return subq;
}

void destroy_query(query *q)
{
	free(q->trails);
	free(q->choices);

	for (arena *a = q->arenas; a;) {
		for (idx_t i = 0; (i < a->hp) && (a == q->arenas); i++) {
			cell *c = &a->heap[i];

			if (is_bigstring(c) && !is_const(c))
				free(c->val_str);
			else if (is_integer(c) && ((c)->flags&FLAG_STREAM)) {
				stream *str = &g_streams[c->val_int];

				if (str->fp) {
					fclose(str->fp);
					free(str->filename);
					free(str->mode);
					free(str->data);
					free(str->name);
					memset(str, 0, sizeof(stream));
				}
			}
		}

		arena *save = a;
		a = a->next;
		free(save->heap);
		free(save);
	}

	for (int i = 0; i < MAX_QUEUES; i++)
		free(q->queue[i]);

	free(q->frames);
	free(q->slots);
	free(q->tmp_heap);
	free(q);
}

static void dump_vars(query *q, parser *p)
{
	frame *g = GET_FRAME(0);
	slot *e = GET_SLOT(g, 0);
	int any = 0;

	for (unsigned i = 0; i < g->nbr_vars; i++, e++) {
		cell *c;

		if (is_empty(&e->c))
			continue;

		if (is_indirect(&e->c))
			c = e->c.val_cell;
		else
			c = GET_VALUE(q, &e->c, 0);

		fprintf(stdout, "\n%s = ", p->vartab.var_name[i]);
		int save = q->quoted;
		q->quoted = 1;
		write_term(q, stdout, c, 1, q->m->dq, 0, 999, 0);
		q->quoted = save;
		any++;
	}

	if (any)
		fprintf(stdout, "\n\n");
}

static void consultall(parser *p, cell *l)
{
	while (is_list(l)) {
		cell *c = l + 1;
		module_load_file(p->m, GET_STR(c));
		l = c + c->nbr_cells;
	}

	p->skip = 1;
}

static int module_load_text(module *m, const char *src);

static void directives(parser *p, term *t)
{
	p->skip = 0;

	if (!is_literal(t->cells))
		return;

	if (is_list(t->cells) && p->command) {
		consultall(p, t->cells);
		return;
	}

	if (strcmp(GET_STR(t->cells), ":-") || (t->cells->arity != 1))
		return;

	cell *c = t->cells + 1;

	if (!is_literal(c))
		return;

	const char *dir = GET_STR(c);

	if (!strcmp(dir, "initialization"))
		return;

	if (!strcmp(dir, "include") && (c->arity == 1)) {
		cell *p1 = c + 1;
		if (!is_literal(p1)) return;
		const char *name = GET_STR(p1);
		int save_line_nbr = p->line_nbr;
		module_load_file(p->m, name);
		p->line_nbr = save_line_nbr;
		return;
	}

	if (!strcmp(dir, "module") && (c->arity == 2)) {
		cell *p1 = c + 1, *p2 = c + 2;
		if (!is_literal(p1)) return;
		const char *name = GET_STR(p1);

		if (find_module(name)) {
			fprintf(stderr, "Error: module already loaded: %s\n", name);
			p->error = 1;
			return;
		}

		p->m = create_module(name);

		while (is_list(p2)) {
			cell *head = p2 + 1;

			if (is_structure(head)) {
				cell *f = head+1, *a = f+1;
				if (!is_literal(f)) return;
				if (!is_integer(a)) return;
				cell tmp;
				tmp.val_type = TYPE_LITERAL;
				tmp.val_offset = find_in_pool(GET_STR(f));
				tmp.arity = a->val_int;
				rule *h = create_rule(p->m, &tmp);
				h->flags |= FLAG_RULE_PUBLIC;
			}

			cell *tail = head + head->nbr_cells;
			p2 = tail;
		}

		return;
	}

	if ((!strcmp(dir, "use_module") || !strcmp(dir, "ensure_loaded")) && (c->arity == 1)) {
		cell *p1 = c + 1;
		if (!is_literal(p1)) return;
		const char *name = GET_STR(p1);

		if (!strcmp(name, "library")) {
			p1 = p1 + 1;
			if (!is_literal(p1)) return;
			name = GET_STR(p1);

			if (find_module(name))
				return;

			for (library *lib = g_libs; lib->name; lib++) {
				if (strcmp(lib->name, name))
					continue;

				char *src = strndup((const char*)lib->start, (lib->end - lib->start));
				module_load_text(p->m, src);
				free(src);
				return;
			}

			return;
		}

		module_load_file(p->m, name);
		return;
	}

	if (!strcmp(dir, "dynamic") && (c->arity >= 1)) {
		cell *p1 = c + 1;

		while (!is_end(p1)) {
			if (!is_literal(p1)) return;
			if (is_literal(p1) && !strcmp(GET_STR(p1), "/") && (p1->arity == 2)) {
				cell *c_name = p1 + 1;
				if (!is_literal(c_name)) return;
				cell *c_arity = p1 + 2;
				if (!is_integer(c_arity)) return;
				set_dynamic_in_db(p->m, GET_STR(c_name), c_arity->val_int);
				p1 += p1->nbr_cells;
			} else
				p1 += 1;
		}

		return;
	}

	if (!strcmp(dir, "persist") && (c->arity >= 1)) {
		cell *p1 = c + 1;

		while (!is_end(p1)) {
			if (!is_literal(p1)) return;
			if (is_literal(p1) && !strcmp(GET_STR(p1), "/") && (p1->arity == 2)) {
				cell *c_name = p1 + 1;
				if (!is_literal(c_name)) return;
				cell *c_arity = p1 + 2;
				if (!is_integer(c_arity)) return;
				set_persist_in_db(p->m, GET_STR(c_name), c_arity->val_int);
				p1 += p1->nbr_cells;
			} else
				p1 += 1;
		}

		return;
	}

	if (!strcmp(dir, "volatile") && (c->arity >= 1)) {
		cell *p1 = c + 1;

		while (!is_end(p1)) {
			if (!is_literal(p1)) return;
			if (is_literal(p1) && !strcmp(GET_STR(p1), "/") && (p1->arity == 2)) {
				cell *c_name = p1 + 1;
				if (!is_literal(c_name)) return;
				cell *c_arity = p1 + 2;
				if (!is_integer(c_arity)) return;
				set_volatile_in_db(p->m, GET_STR(c_name), c_arity->val_int);
				p1 += p1->nbr_cells;
			} else
				p1 += 1;
		}

		return;
	}

	if (!strcmp(dir, "set_prolog_flag") && (c->arity == 2)) {
		cell *p1 = c + 1, *p2 = c + 2;
		if (!is_literal(p1)) return;
		if (!is_literal(p2)) return;

		if (!strcmp(GET_STR(p1), "double_quotes")) {
			if (!strcmp(GET_STR(p2), "atom")) {
				p->m->flag.double_quote_chars = p->m->flag.double_quote_codes = 0;
				p->m->flag.double_quote_atom = 1;
			} else if (!strcmp(GET_STR(p2), "codes")) {
				p->m->flag.double_quote_chars = p->m->flag.double_quote_atom = 0;
				p->m->flag.double_quote_codes = 1;
			} else if (!strcmp(GET_STR(p2), "chars")) {
				p->m->flag.double_quote_atom = p->m->flag.double_quote_codes = 0;
				p->m->flag.double_quote_chars = 1;
			} else {
				fprintf(stderr, "Error: unknown value\n");
				p->error = 1;
				return;
			}
		} else if (!strcmp(GET_STR(p1), "character_escapes")) {
			if (!strcmp(GET_STR(p2), "true"))
				p->m->flag.character_escapes = 1;
			else if (!strcmp(GET_STR(p2), "false"))
				p->m->flag.character_escapes = 0;
		} else if (!p->m->iso_only && !strcmp(GET_STR(p1), "prefer_rationals")) {
			if (!strcmp(GET_STR(p2), "true"))
				p->m->flag.prefer_rationals = 1;
			else if (!strcmp(GET_STR(p2), "false"))
				p->m->flag.prefer_rationals = 0;
		} else if (!p->m->iso_only && !strcmp(GET_STR(p1), "rational_syntax")) {
			if (!strcmp(GET_STR(p2), "natural"))
				p->m->flag.rational_syntax_natural = 1;
			else if (!strcmp(GET_STR(p2), "compatibility"))
				p->m->flag.rational_syntax_natural = 0;
		} else {
			fprintf(stderr, "Error: unknown flag\n");
			p->error = 1;
			return;
		}

		return;
	}

	if (!strcmp(dir, "op") && (c->arity == 3)) {
		cell *p1 = c + 1, *p2 = c + 2, *p3 = c + 3;

		if (!is_integer(p1) || !is_literal(p2) || !is_atom(p3)) {
			fprintf(stderr, "Error: unknown op\n");
			p->error = 1;
			return;
		}

		unsigned optype;
		const char *spec = GET_STR(p2);

		if (!strcmp(spec, "fx"))
			optype = OP_FX;
		else if (!strcmp(spec, "fy"))
			optype = OP_FY;
		else if (!strcmp(spec, "xf"))
			optype = OP_XF;
		else if (!strcmp(spec, "xfx"))
			optype = OP_XFX;
		else if (!strcmp(spec, "xfy"))
			optype = OP_XFY;
		else if (!strcmp(spec, "yf"))
			optype = OP_YF;
		else if (!strcmp(spec, "yfx"))
			optype = OP_YFX;
		else {
			fprintf(stderr, "Error: unknown op spec val_type\n");
			return;
		}

		if (!set_op(p->m, GET_STR(p3), optype, p1->val_int)) {
			fprintf(stderr, "Error: could not set op\n");
			return;
		}
	}
}

int parser_xref(parser *p, term *t, rule *parent)
{
	for (idx_t i = 0; i < t->cidx; i++) {
		cell *c = t->cells + i;

		if (!is_literal(c))
			continue;

		const char *functor = GET_STR(c);
		module *m = p->m;

		if ((c->fn = get_builtin(m, functor, c->arity)) != NULL) {
			c->flags |= FLAG_BUILTIN;
			continue;
		}

		if (check_builtin(m, functor, c->arity)) {
			c->flags |= FLAG_BUILTIN;
			continue;
		}

		if (strchr(functor, ':')) {
			char tmpbuf1[256], tmpbuf2[256];
			tmpbuf1[0] = tmpbuf2[0] = '\0';
			sscanf(functor, "%255[^:]:%255s", tmpbuf1, tmpbuf2);
			tmpbuf1[sizeof(tmpbuf1)-1] = tmpbuf2[sizeof(tmpbuf2)-1] = '\0';
			m = find_module(tmpbuf1);

			if (m)
				c->val_offset = find_in_pool(tmpbuf2);
			else
				m = p->m;
		}

		module *tmp_m = NULL;

		while (m) {
			rule *h = find_match(m, c);

			if ((c+c->nbr_cells) >= (t->cells+t->cidx-1)) {
				if (parent && (h == parent))
					c->flags |= FLAG_TAILREC;

				c->flags |= FLAG_TAIL;
			}

			if (h && (m != p->m) && !(h->flags&FLAG_RULE_PUBLIC)) {
				fprintf(stderr, "Error: not a public method\n");
				p->error = 1;
				return 0;
			}

			if (h) {
				c->match = h;
				break;
			}

			if (!tmp_m)
				m = tmp_m = g_modules;
			else
				m = m->next;
		}
	}

	return 1;
}

static void parser_xref_db(parser *p)
{
	for (rule *h = p->m->head; h; h = h->next) {
		for (clause *r = h->head; r; r = r->next)
			parser_xref(p, &r->t, h);
	}
}

static void check_first_cut(parser *p)
{
	cell *c = get_body(p->m, p->t->cells);
	int cut_only = 1;

	if (!c)
		return;

	while (!is_end(c)) {
		if (!(c->flags&FLAG_BUILTIN))
			break;

		if (!strcmp(GET_STR(c), ","))
			;
		else if (!strcmp(GET_STR(c), "!")) {
			p->t->first_cut = 1;
			break;
		} else {
			cut_only = 0;
			break;
		}

		c += c->nbr_cells;
	}

	if (p->t->first_cut && cut_only)
		p->t->cut_only = 1;
}

static idx_t get_varno(parser *p, const char *src)
{
	int anon = !strcmp(src, "_");
	size_t offset = 0;
	int i = 0;

	while (p->vartab.var_pool[offset]) {
		if (!strcmp(p->vartab.var_pool+offset, src) && !anon)
			return i;

		offset += strlen(p->vartab.var_pool+offset) + 1;
		i++;
	}

	size_t len = strlen(src);

	if ((offset+len+1) >= MAX_VAR_POOL_SIZE) {
		fprintf(stderr, "Error: var pool exhausted\n");
		p->error = 1;
		return 0;
	}

	strcpy(p->vartab.var_pool+offset, src);
	return i;
}

void parser_assign_vars(parser *p)
{
	p->start_term = 1;
	memset(&p->vartab, 0, sizeof(p->vartab));
	term *t = p->t;
	t->nbr_vars = 0;
	t->first_cut = 0;
	t->cut_only = 0;

	for (idx_t i = 0; i < t->cidx; i++) {
		cell *c = t->cells + i;

		if (!is_var(c))
			continue;

		c->slot_nbr = get_varno(p, GET_STR(c));

		if (c->slot_nbr == MAX_ARITY) {
			fprintf(stderr, "Error: max vars per term reached\n");
			p->error = 1;
			return;
		}

		p->vartab.var_name[c->slot_nbr] = GET_STR(c);

		if (p->vartab.var_used[c->slot_nbr]++ == 0) {
			c->flags |= FLAG_FIRST_USE;
			t->nbr_vars++;
		}
	}

	for (idx_t i = 0; i < t->nbr_vars; i++) {
		if (p->consulting && (p->vartab.var_used[i] == 1) && (*p->vartab.var_name[i] != '_')) {
			if (!p->m->quiet)
				fprintf(stderr, "Warning: singleton: %s, line %d\n", p->vartab.var_name[i], (int)p->line_nbr);
		}
	}

	cell *c = make_cell(p);
	memset(c, 0, sizeof(cell));
	c->val_type = TYPE_END;
	c->nbr_cells = 1;

	check_first_cut(p);
	directives(p, t);
}

static int attach_ops(parser *p, idx_t start_idx)
{
	idx_t lowest = INT_MAX, work_idx;
	int do_work = 0;

	for (idx_t i = start_idx; i < p->t->cidx;) {
		cell *c = p->t->cells + i;

		if (c->nbr_cells > 1) {
			i += c->nbr_cells;
			continue;
		}

		if (!is_literal(c) || !c->precedence) {
			i++;
			continue;
		}

		if ((c->flags&OP_XFY) || (c->flags&OP_FY)) {
			if (c->precedence <= lowest) {
				lowest = c->precedence;
				work_idx = i;
				do_work = 1;
			}
		} else {
			if (c->precedence < lowest) {
				lowest = c->precedence;
				work_idx = i;
				do_work = 1;
			}
		}

		i++;
	}

	if (!do_work)
		return 0;

	idx_t last_idx = 0;

	for (idx_t i = start_idx; i < p->t->cidx;) {
		cell *c = p->t->cells + i;

		if (c->nbr_cells > 1) {
			last_idx = i;
			i += c->nbr_cells;
			continue;
		}

		if (!is_literal(c) || !c->precedence) {
			last_idx = i;
			i++;
			continue;
		}

		if ((c->precedence != lowest) || (i != work_idx)) {
			last_idx = i;
			i++;
			continue;
		}

		c->val_type = TYPE_LITERAL;
		c->arity = 1;

		// Prefix...

		if ((c->flags&OP_FX) || (c->flags&OP_FY)) {
			last_idx = i;
			c->nbr_cells += (c+1)->nbr_cells;
			i += c->nbr_cells;

			if (((c+1)-p->t->cells) >= p->t->cidx) {
				//fprintf(stderr, "Error: missing operand to '%s'\n", GET_STR(c));
				//p->error = 1;
				c->arity = 0;
				return 0;
			}

			continue;
		}

		// Infix...

		if (!(c->flags&OP_XF) && !(c->flags&OP_YF)) {
			if (((c+1)-p->t->cells) >= p->t->cidx) {
				//fprintf(stderr, "Error: missing operand to '%s'\n", GET_STR(c));
				//p->error = 1;
				return 0;
			}

			c->arity = 2;
		}

		// Infix and Postfix...

		cell save = *c;

		if (!(c->flags&OP_XF) && !(c->flags&OP_YF))
			save.nbr_cells += (c+1)->nbr_cells;

		cell *c_last = p->t->cells + last_idx;
		idx_t cells_to_move = c_last->nbr_cells;
		c_last = c-1;

		while (cells_to_move--)
			*c-- = *c_last--;

		*c = save;
		c->nbr_cells += (c+1)->nbr_cells;
		i += c->nbr_cells;
		break;
	}

	return 1;
}

int parser_attach(parser *p, int start_idx)
{
	while (attach_ops(p, start_idx))
		;

	return !p->error;
}

static void parser_dcg_rewrite(parser *p)
{
	p->in_dcg = 0;
	term *t = p->t;

	if (!is_literal(t->cells))
		return;

	if (strcmp(GET_STR(t->cells), "-->") || (t->cells->arity != 2))
		return;

	cell *phrase = t->cells + 1;
	cell *tmp = calloc(1+(t->cidx*4), sizeof(cell));
	*tmp = t->cells[0];
	tmp->val_offset = find_in_pool(":-");
	idx_t nbr_cells = 1;
	int cnt = 0, head = 1, insert = 0;

	while ((phrase - t->cells) < t->cidx) {
		if (!strcmp(GET_STR(phrase), ",") && phrase->arity && head) {
			phrase++;
			insert++;
			continue;
		}

		if (!strcmp(GET_STR(phrase), ",") && phrase->arity) {
			tmp[nbr_cells++] = *phrase;
			phrase++;
			continue;
		}

		int last = ((phrase+phrase->nbr_cells) - t->cells) >= t->cidx;

		if (!strcmp(GET_STR(phrase), "{}") && phrase->arity) {
			idx_t len = phrase->nbr_cells - 1;
			cell *phrase2 = phrase + phrase->nbr_cells;

			if (last && ((phrase2 - t->cells) >= t->cidx)) {
				tmp[nbr_cells].val_type = TYPE_LITERAL;
				tmp[nbr_cells].val_offset = find_in_pool(",");
				tmp[nbr_cells].nbr_cells = 2 + len;
				tmp[nbr_cells].arity = 2;
				tmp[nbr_cells].flags = FLAG_BUILTIN | OP_XFY;
				nbr_cells++;
			}

			copy_cells(tmp+nbr_cells, phrase+1, len);
			nbr_cells += len;
			phrase += phrase->nbr_cells;

			if (last && ((phrase - t->cells) >= t->cidx)) {
				tmp[nbr_cells+0].val_type = TYPE_LITERAL;
				tmp[nbr_cells+0].val_offset = find_in_pool("=");
				tmp[nbr_cells+0].nbr_cells = 3;
				tmp[nbr_cells+0].arity = 2;
				tmp[nbr_cells+0].flags = FLAG_BUILTIN | OP_XFX;

				tmp[nbr_cells+1].val_type = TYPE_VAR;
				tmp[nbr_cells+1].nbr_cells = 1;
				char v[20]; sprintf(v, "S_");
				tmp[nbr_cells+1].val_offset = find_in_pool(v);

				tmp[nbr_cells+2].val_type = TYPE_VAR;
				tmp[nbr_cells+2].nbr_cells = 1;
				sprintf(v, "S%d_", cnt++);
				tmp[nbr_cells+2].val_offset = find_in_pool(v);

				nbr_cells += 3;
			}

			continue;
		}

		if (is_list(phrase) && insert) {
			tmp[nbr_cells+0].val_type = TYPE_LITERAL;
			tmp[nbr_cells+0].val_offset = find_in_pool("=");
			tmp[nbr_cells+0].nbr_cells = 5;
			tmp[nbr_cells+0].arity = 2;
			tmp[nbr_cells+0].flags = FLAG_BUILTIN | OP_XFX;

			tmp[nbr_cells+1].val_type = TYPE_VAR;
			tmp[nbr_cells+1].nbr_cells = 1;
			char v[20]; sprintf(v, "S_");
			tmp[nbr_cells+1].val_offset = find_in_pool(v);

			tmp[nbr_cells+2] = phrase[0];
			tmp[nbr_cells+2].nbr_cells = 3;
			tmp[nbr_cells+2].arity = 2;

			tmp[nbr_cells+3] = phrase[1];

			tmp[nbr_cells+4].val_type = TYPE_VAR;
			tmp[nbr_cells+4].nbr_cells = 1;
			if (last) { sprintf(v, "S_"); last = 0; }
			else sprintf(v, "S%d_", cnt++);
			tmp[nbr_cells+4].val_offset = find_in_pool(v);

			nbr_cells += 5;
			phrase += phrase->nbr_cells;
		} else if (is_list(phrase)) {
			int len = phrase[0].nbr_cells;
			tmp[nbr_cells+0].val_type = TYPE_LITERAL;
			tmp[nbr_cells+0].val_offset = find_in_pool("=");
			tmp[nbr_cells+0].nbr_cells = 2 + len;
			tmp[nbr_cells+0].arity = 2;
			tmp[nbr_cells+0].flags = FLAG_BUILTIN | OP_XFX;

			tmp[nbr_cells+1].val_type = TYPE_VAR;
			tmp[nbr_cells+1].nbr_cells = 1;
			char v[20]; sprintf(v, "S%d_", cnt);
			tmp[nbr_cells+1].val_offset = find_in_pool(v);

			copy_cells(tmp+nbr_cells+2, phrase, len);

			tmp[nbr_cells+2+len-1].val_type = TYPE_VAR;
			tmp[nbr_cells+2+len-1].nbr_cells = 1;
			if (last) { sprintf(v, "S_"); last = 0; }
			else sprintf(v, "S%d_", ++cnt);
			tmp[nbr_cells+2+len-1].val_offset = find_in_pool(v);
			tmp[nbr_cells+2+len-1].flags = 0;

			nbr_cells += 2+len;
			phrase += phrase->nbr_cells;
		} else if (is_nil(phrase)) {
			tmp[nbr_cells+0].val_type = TYPE_LITERAL;
			tmp[nbr_cells+0].val_offset = find_in_pool("=");
			tmp[nbr_cells+0].nbr_cells = 3;
			tmp[nbr_cells+0].arity = 2;
			tmp[nbr_cells+0].flags = FLAG_BUILTIN | OP_XFX;

			tmp[nbr_cells+1].val_type = TYPE_VAR;
			tmp[nbr_cells+1].nbr_cells = 1;
			char v[20]; sprintf(v, "S%d_", cnt);
			tmp[nbr_cells+1].val_offset = find_in_pool(v);

			tmp[nbr_cells+2].val_type = TYPE_VAR;
			tmp[nbr_cells+2].nbr_cells = 1;
			sprintf(v, "S_");
			tmp[nbr_cells+2].val_offset = find_in_pool(v);

			nbr_cells += 3;
			phrase += phrase->nbr_cells;
		} else {
			copy_cells(tmp+nbr_cells, phrase, phrase->nbr_cells);

			tmp[nbr_cells+phrase->nbr_cells+0].val_type = TYPE_VAR;
			tmp[nbr_cells+phrase->nbr_cells+0].nbr_cells = 1;
			char v[20]; sprintf(v, "S%d_", cnt);
			tmp[nbr_cells+phrase->nbr_cells+0].val_offset = find_in_pool(v);

			tmp[nbr_cells+phrase->nbr_cells+1].val_type = TYPE_VAR;
			tmp[nbr_cells+phrase->nbr_cells+1].nbr_cells = 1;
			if (head || last) { sprintf(v, "S_"); last = 0; }
			else sprintf(v, "S%d_", ++cnt);
			tmp[nbr_cells+phrase->nbr_cells+1].val_offset = find_in_pool(v);

			tmp[nbr_cells].nbr_cells += 2;
			tmp[nbr_cells].arity += 2;
			nbr_cells += 2;

			nbr_cells += phrase->nbr_cells;
			phrase += phrase->nbr_cells;
		}

		head = 0;
	}

	tmp->nbr_cells = nbr_cells;
	nbr_cells++;	// spare
	p->t = realloc(p->t, sizeof(term)+(sizeof(cell)*nbr_cells));
	copy_cells(p->t->cells, tmp, nbr_cells-1);
	p->t->nbr_cells = nbr_cells;
	p->t->cidx = tmp->nbr_cells;
	free(tmp);
}

static cell *make_literal(parser *p, idx_t offset)
{
	cell *c = make_cell(p);
	memset(c, 0, sizeof(cell));
	c->val_type = TYPE_LITERAL;
	c->nbr_cells = 1;
	c->val_offset = offset;
	return c;
}

static int parse_number(parser *p, const char **srcptr, int_t *val_num, int_t *val_den)
{
	*val_den = 1;
	const char *s = *srcptr;
	int neg = 0;

	if (*s == '-') {
		neg = 1;
		s++;
	} else if (*s == '+') {
		s++;
	}

	if ((*s == '0') && (s[1] == '\'')) {
		s += 2;
		int v = get_char_utf8(&s);
		*val_num = v;
		if (neg) *val_num = -*val_num;
		*srcptr = s;
		return 1;
	}

	if ((*s == '0') && (s[1] == 'b')) {
		uint_t v = 0;
		s += 2;

		while ((*s == '0') || (*s == '1')) {
			v <<= 1;

			if (*s == '1')
				v |= 1;

			s++;
		}

		*((uint_t*)val_num) = v;
		if (neg) *val_num = -*val_num;
		*srcptr = s;
		return 1;
	}

	if ((*s == '0') && (s[1] == 'o')) {
		uint_t v = 0;
		s += 2;

		while ((*s >= '0') && (*s <= '7')) {
			v *= 8;
			v += *s - '0';
			s++;
		}

		*((uint_t*)val_num) = v;
		if (neg) *val_num = -*val_num;
		*srcptr = s;
		return 1;
	}

	if ((*s == '0') && (s[1] == 'x')) {
		uint_t v = 0;
		s += 2;

		while (((*s >= '0') && (*s <= '9')) || ((toupper(*s) >= 'A') && (toupper(*s) <= 'F'))) {
			v *= 16;

			if ((toupper(*s) >= 'A') && (toupper(*s) <= 'F'))
				v += 10 + (toupper(*s) - 'A');
			else
				v += *s - '0';

			s++;
		}

		*((uint_t*)val_num) = v;
		if (neg) *val_num = -*val_num;
		*srcptr = s;
		return 1;
	}

	if (isdigit(*s)) {
		char *tmpptr;
		strtod(s, &tmpptr);
		if (tmpptr[-1] == '.') tmpptr--;
		*val_num = atoll(s);
		if (neg) *val_num = -*val_num;
		int try_rational = 0;

		if (!p->m->iso_only && ((tmpptr[0] == 'r') || (tmpptr[0] == 'R')))
			try_rational = 1;
		else if (!p->m->iso_only && (tmpptr[0] == '/') && p->m->flag.rational_syntax_natural)
			try_rational = 1;

		if (try_rational && isdigit(tmpptr[1]) ) {
			s = tmpptr + 1;
			strtod(s, &tmpptr);
			if (tmpptr[-1] == '.') tmpptr--;
			*val_den = atoll(s);

			cell tmp;
			tmp.val_num = *val_num;
			tmp.val_den = *val_den;
			do_reduce(&tmp);
			*val_num = tmp.val_num;
			*val_den = tmp.val_den;
		}

		*srcptr = tmpptr;
		return 1;
	}

	return 0;
}

static int get_octal(const char **srcptr)
{
	const char *src = *srcptr;
	int v = 0;

	while (*src == '0')
		src++;

	while ((*src >= '0') && (*src <= '7')) {
		v *= 8;
		char ch = *src++;
		v += ch - '0';
	}

	*srcptr = src;
	return v;
}

static int get_hex(const char **srcptr, int n)
{
	const char *src = *srcptr;
	int v = 0;

	while ((n > 0) && *src == '0') {
		src++; n--;
	}

	while ((n > 0) && (((*src >= '0') && (*src <= '9')) ||
		((*src >= 'a') && (*src <= 'f')) ||
		((*src >= 'A') && (*src <= 'F')))) {
		v *= 16;
		char ch = *src++;
		n--;

		if ((ch >= 'a') && (ch <= 'f'))
			v += 10 + (ch - 'a');
		else if ((ch >= 'A') && (ch <= 'F'))
			v += 10 + (ch - 'A');
		else
			v += ch - '0';
	}

	*srcptr = src;
	return v;
}

const char *g_escapes = "\e\a\f\b\t\v\r\n";
const char *g_anti_escapes = "eafbtvrn";

static int get_escape(const char **_src, int *error)
{
	const char *src = *_src;
	int ch = *src++;
	const char *ptr = strchr(g_anti_escapes, ch);

	if (ptr)
		ch = g_escapes[ptr-g_anti_escapes];
	else if (isdigit(ch) || (ch == 'x') || (ch == 'u') || (ch == 'U')) {
		int unicode = 0;

		if (ch == 'U') {
			ch = get_hex(&src, 8);
			unicode = 1;
		} else if (ch == 'u') {
			ch = get_hex(&src, 4);
			unicode = 1;
		} else if (ch == 'x')
			ch = get_hex(&src, 999);
		else {
			src--;
			ch = get_octal(&src);
		}

		if (!unicode && (*src++ != '\\')) {
			fprintf(stderr, "Error: closing \\ missing\n");
			*_src = src;
			*error = 1;
			return 0;
		}
	}

	*_src = src;
	return ch;
}

static int get_token(parser *p, int last_op)
{
	const char *src = p->srcptr;
	char *dst = p->token;
	int neg = 0;
	p->val_type = TYPE_LITERAL;
	p->quoted = p->is_var = p->is_op = 0;
	*dst = '\0';

	if (p->dq_consing && (*src == '"') && !p->m->flag.double_quote_atom) {
		*dst++ = ']';
		*dst = '\0';
		p->srcptr = (char*)++src;
		p->dq_consing = 0;
		return 1;
	}

	if (p->dq_consing < 0) {
		*dst++ = ',';
		*dst = '\0';
		p->dq_consing = 1;
		return 1;
	}

	if (p->dq_consing && p->m->flag.double_quote_codes) {
		int ch = get_char_utf8(&src);

		if ((ch == '\\') && p->m->flag.character_escapes) {
			ch = get_escape(&src, &p->error);

			if (p->error) {
				fprintf(stderr, "Error: illegal character escape, line %d\n", p->line_nbr);
				p->error = 1;
				return 0;
			}
		}

		dst += sprintf(dst, "%u", ch);
		*dst = '\0';
		p->srcptr = (char*)src;
		p->val_type = TYPE_INT;
		p->dq_consing = -1;
		return 1;
	}

	if (p->dq_consing && p->m->flag.double_quote_chars) {
		int ch = get_char_utf8(&src);
		dst += put_char_utf8(dst, ch);
		*dst = '\0';
		p->srcptr = (char*)src;
		p->quoted = 1;
		p->dq_consing = -1;
		return 1;
	}

	while (isspace(*src)) {
		if (*src == '\n')
			p->line_nbr++;

		src++;
	}

	if ((*src == '%') && !p->fp) {
		while (*src && (*src != '\n'))
			src++;

		if (*src == '\n')
			p->line_nbr++;

		src++;
	}

	if ((!*src || (*src == '%')) && p->fp) {
		if (*src == '%')
			p->line_nbr++;

		if (getline(&p->save_line, &p->n_line, p->fp) == -1)
			return 0;

		p->srcptr = p->save_line;
		src = p->srcptr;

		while (isspace(*src)) {
			if (*src == '\n')
				p->line_nbr++;

			src++;
		}
	}

	if (!*src) {
		p->srcptr = (char*)src;
		return 0;
	}

	if (*src == '%')
		return 0;

	do {
		if (!p->comment && (src[0] == '/') && (src[1] == '*')) {
			p->comment = 1;
			src += 2;
			continue;
		}

		if (p->comment && (src[0] == '*') && (src[1] == '/')) {
			p->comment = 0;
			src += 2;
			p->srcptr = (char*)src;
			return get_token(p, last_op);
		}

		if (p->comment)
			src++;

		if (!*src && p->comment && p->fp) {
			if (getline(&p->save_line, &p->n_line, p->fp) == -1) {
				p->srcptr = (char*)src;
				return 1;
			}

			src = p->srcptr = p->save_line;
				p->line_nbr++;
		}
	}
	 while (*src && p->comment);

	// (+/-)tive numbers...

	if (((*src == '-') || (*src == '+')) && last_op) {
		const char *save_src = src++;

		while (isspace(*src)) {
			if (*src == '\n')
				p->line_nbr++;

			src++;
		}

		if (isdigit(*src)) {
			if (*save_src == '-')
				neg = 1;
		} else
			src = save_src;
	}

	// Numbers...

	const char *tmpptr = src;
	int_t v = 0, d = 1;

	if ((*src != '-') && (*src != '+') && parse_number(p, &src, &v, &d)) {
		if (neg)
			*dst++ = '-';

		// There is room for a number...

		if ((src-tmpptr) >= p->token_size) {
			size_t len = dst - p->token;
			p->token = realloc(p->token, p->token_size*=2);
			if (!p->token) abort();
			dst = p->token+len;
		}

		strncpy(dst, tmpptr, src-tmpptr);
		dst[src-tmpptr] = '\0';

		if (strchr(dst, '.') || strchr(dst, 'e') || strchr(dst, 'E'))
			p->val_type = TYPE_FLOAT;
		else
			p->val_type = TYPE_INT;

		p->srcptr = (char*)src;
		return 1;
	}

	// Quoted strings...

	if ((*src == '"') || (*src == '`') || (*src == '\'')) {
		p->quoted = *src++;

		if ((p->quoted == '"') && !p->m->flag.double_quote_atom) {
			*dst++ = '[';
			*dst = '\0';
			p->srcptr = (char*)src;
			p->dq_consing = 1;
			p->quoted = 0;
			return 1;
		}

		for (;;) {
			while (*src) {
				int ch = get_char_utf8(&src);

				if (ch == p->quoted) {
					p->quoted = 0;
					break;
				}

				if ((ch == '\\') && p->m->flag.character_escapes) {
					int ch2 = *src;
					ch = get_escape(&src, &p->error);

					if (!p->error) {
						if (ch2 == '\n') {
							p->line_nbr++;
							break;
						}
					} else {
						fprintf(stderr, "Error: illegal character escape, line %d\n", p->line_nbr);
						p->error = 1;
						return 0;
					}
				}

				int len = (dst-p->token) + put_len_utf8(ch) + 1;

				if (len >= p->token_size) {
					size_t len = dst - p->token;
					p->token = realloc(p->token, p->token_size*=2);
					if (!p->token) abort();
					dst = p->token+len;
				}

				dst += put_char_utf8(dst, ch);
				*dst = '\0';
			}

			if (p->quoted && p->fp) {
				if (getline(&p->save_line, &p->n_line, p->fp) == -1) {
					p->srcptr = (char*)src;
					return 1;
				}

				src = p->srcptr = p->save_line;
				continue;
			}

			int userop = 0;

			if (get_op(p->m, p->token, NULL, &userop, 0)) {
				if (userop)
					p->is_op = 1;

				if (!strcmp(p->token, ","))
					p->quoted = 1;
			} else
				p->quoted = 1;

			p->srcptr = (char*)src;
			return 1;
		}
	}

	int ch = peek_char_utf8(src);

	// Atoms...

	if (isalpha_utf8(ch) || (ch == '_')) {
		while (isalnum_utf8(ch) || (ch == '_') ||
			((ch == ':') && find_module(p->token))) {
			ch = get_char_utf8(&src);

			int len = (dst-p->token) + put_len_utf8(ch) + 1;

			if (len >= p->token_size) {
				size_t len = dst - p->token;
				p->token = realloc(p->token, p->token_size*=2);
				if (!p->token) abort();
				dst = p->token+len;
			}

			dst += put_char_utf8(dst, ch);
			*dst = '\0';
			ch = peek_char_utf8(src);
		}

		if (isupper(*p->token) || (*p->token == '_'))
			p->is_var = 1;
		else if (get_op(p->m, p->token, NULL, NULL, 0))
			p->is_op = 1;

		p->srcptr = (char*)src;
		return 1;
	}

	if (((src[0] == '[') && (src[1] == ']')) ||
		//((src[0] == '(') && (src[1] == ')')) ||		// Non-ISO
		((src[0] == '{') && (src[1] == '}'))) {
		*dst++ = *src++;
		*dst++ = *src++;
		*dst = '\0';
		p->srcptr = (char*)src;
		return (dst-p->token) > 0;
	}

	if (src[0] == '!') {
		*dst++ = *src++;
		*dst = '\0';
		p->srcptr = (char*)src;
		return (dst-p->token) > 0;
	}

	static const char *s_delims = "(){}[]_, `'\"\t\r\n";
	p->is_op = 1;

	while (*src) {
		ch = get_char_utf8(&src);
		int len = (dst-p->token) + put_len_utf8(ch) + 1;

		if (len >= p->token_size) {
			size_t len = dst - p->token;
			p->token = realloc(p->token, p->token_size*=2);
			if (!p->token) abort();
			dst = p->token+len;
		}

		dst += put_char_utf8(dst, ch);
		*dst = '\0';

		if (strchr(s_delims, ch))
			break;

		ch = peek_char_utf8(src);

		if (strchr(s_delims, ch) || isalnum_utf8(ch) || (ch == '_'))
			break;
	}

	p->srcptr = (char*)src;
	return 1;
}

int parser_tokenize(parser *p, int args, int consing)
{
	int begin_idx = p->t->cidx;
	int last_op = 1;
	unsigned arity = 1;
	int is_func = 0, save_idx = 0;
	p->depth++;

	while (get_token(p, last_op)) {
		if (p->error)
			break;

		//fprintf(stderr, "Debug: token '%s' quoted=%d, val_type=%u, op=%d, lastop=%d\n", p->token, p->quoted, p->val_type, p->is_op, last_op);

		if (!p->quoted && !strcmp(p->token, ".") && (*p->srcptr != '(') && (*p->srcptr != ',') && (*p->srcptr != ')')) {
			if (parser_attach(p, 0)) {
				parser_dcg_rewrite(p);
				parser_assign_vars(p);

				if (p->consulting && !p->skip)
					if (!assertz_to_db(p->m, p->t, 1)) {
						printf("Error: '%s', line nbr %d\n", p->token, p->line_nbr);
						p->error = 1;
					}
			}

			p->end_of_term = 1;
			last_op = 1;

			if (p->one_shot)
				break;

			continue;
		}

        if (p->in_dcg && !p->quoted && !strcmp(p->token, "|") && !p->dcg_passthru) {
			strcpy(p->token, ";");
        } else if (p->in_dcg && !p->quoted && !strcmp(p->token, "{") && !p->dcg_passthru++)
			;
		else if (p->in_dcg && !p->quoted && !strcmp(p->token, "}") && !--p->dcg_passthru)
			;

		if (!p->depth && !p->in_dcg && !p->quoted && !strcmp(p->token, "-->"))
			p->in_dcg = 1;

		if (!p->quoted && !strcmp(p->token, "[")) {
			save_idx = p->t->cidx;
			cell *c = make_literal(p, g_dot_s);
			c->arity = 2;
			p->start_term = 1;
			parser_tokenize(p, 1, 1);

			if (p->error)
				break;

			c = make_literal(p, g_nil_s);
			c = p->t->cells+save_idx;
			c->nbr_cells = p->t->cidx - save_idx;
			p->start_term = 0;
			last_op = 0;
			continue;
		}

		if (!p->quoted && !strcmp(p->token, "{")) {
			save_idx = p->t->cidx;
			cell *c = make_literal(p, find_in_pool("{}"));
			c->arity = 1;
			p->start_term = 1;
			parser_tokenize(p, 0, 0);

			if (p->error)
				break;

			c = p->t->cells+save_idx;
			c->nbr_cells = p->t->cidx - save_idx;
			p->start_term = 0;
			last_op = 0;
			continue;
		}

		if (!p->quoted && !strcmp(p->token, "(")) {
			p->start_term = 1;
			unsigned tmp_arity = parser_tokenize(p, is_func, 0);

			if (p->error)
				break;

			if (is_func) {
				cell *c = p->t->cells + save_idx;
				c->arity = tmp_arity;
				c->nbr_cells = p->t->cidx - save_idx;
			}

			is_func = 0;
			last_op = 0;
			p->start_term = 0;
			continue;
		}

		if (!p->quoted && !strcmp(p->token, ",") && consing) {
			cell *c = make_literal(p, g_dot_s);
			c->arity = 2;
			p->start_term = 1;
			last_op = 1;
			continue;
		}

		if (!p->quoted && !strcmp(p->token, ",") && args) {
			arity++;

			if (arity > MAX_ARITY) {
				fprintf(stderr, "Error: max arity reached, line %d: %s\n", p->line_nbr, p->srcptr);
				p->error = 1;
				break;
			}

			last_op = 1;
			continue;
		}

		if (!p->quoted && consing && !strcmp(p->token, "|")) {
			consing = 0;
			continue;
		}

		if (!p->quoted && p->start_term &&
			(!strcmp(p->token, ",") || !strcmp(p->token, "]") || !strcmp(p->token, ")") || !strcmp(p->token, "}"))) {
			fprintf(stderr, "Error: start of term expected, line %d: %s\n", p->line_nbr, p->srcptr);
			p->error = 1;
			break;
		}

		if (!p->quoted && (!strcmp(p->token, ")") || !strcmp(p->token, "]") || !strcmp(p->token, "}"))) {
			parser_attach(p, begin_idx);
			return arity;
		}

		if (p->is_var && (*p->srcptr == '(')) {
			fprintf(stderr, "Error: syntax error, line %d: %s\n", p->line_nbr, p->srcptr);
			p->error = 1;
			break;
		}

		unsigned optype = 0;
		int userop = 0;
		int precedence = get_op(p->m, p->token, &optype, &userop, last_op);

		if (p->quoted && !userop) {
			optype = 0;
			precedence = 0;
		}

		if (precedence && ((*p->srcptr == ',') || (*p->srcptr == ')'))) {
			optype = 0;
			precedence = 0;
		}

		// Operators in canonical form..

		if (last_op && precedence && (*p->srcptr == '(')) {
			p->val_type = TYPE_LITERAL;
			optype = 0;
			precedence = 0;
			p->quoted = 0;
		}

		last_op = strcmp(p->token, ")") && precedence;
		int func = (p->val_type == TYPE_LITERAL) && !optype && (*p->srcptr == '(');

		if (func) {
			is_func = 1;
			p->is_op = 0;
			save_idx = p->t->cidx;
		}

#if 0
		if (p->is_op && !precedence) {
			fprintf(stderr, "Error: syntax error or operator expected, line %d: %s, %s\n", p->line_nbr, p->token, p->srcptr);
			p->error = 1;
			break;
		}
#endif

		p->start_term = 0;
		cell *c = make_cell(p);
		memset(c, 0, sizeof(cell));
		c->nbr_cells = 1;
		c->val_type = p->val_type;
		c->flags = (uint16_t)optype;
		c->precedence = precedence;

		if (p->dcg_passthru)
			c->flags |= FLAG_PASSTHRU;

		if (p->val_type == TYPE_INT) {
			const char *src = p->token;
			parse_number(p, &src, &c->val_num, &c->val_den);

			if (strstr(p->token, "0o"))
				c->flags |= FLAG_OCTAL;
			else if (strstr(p->token, "0x"))
				c->flags |= FLAG_HEX;
			else if (strstr(p->token, "0b"))
				c->flags |= FLAG_BINARY;
		}
		else if (p->val_type == TYPE_FLOAT)
			c->val_real = atof(p->token);
		else if (!p->quoted || func || p->is_op || p->is_var || check_builtin(p->m, p->token, 0)) {
			if (func && !strcmp(p->token, "."))
				c->precedence = 0;

			if (p->is_var)
				c->val_type = TYPE_VAR;

			c->val_offset = find_in_pool(p->token);
		} else {
			c->val_type = TYPE_STRING;

			if (strlen(p->token) < MAX_SMALL_STRING) {
				c->flags |= FLAG_SMALL_STRING;
				strcpy(c->val_chars, p->token);
			} else
				c->val_str = strdup(p->token);
		}
	}

	p->depth--;
	return !p->error;
}

static void module_purge(module *m)
{
	if (!m->dirty)
		return;

	for (rule *h = m->head; h != NULL; h = h->next) {
		clause *last = NULL;

		for (clause *r = h->head; r != NULL;) {
			if (!r->t.deleted) {
				last = r;
				r = r->next;
				continue;
			}

			if (h->head == r)
				h->head = r->next;

			if (h->tail == r)
				h->tail = last;

			if (last)
				last->next = r->next;

			clause *next = r->next;
			clear_term(&r->t);
			free(r);
			r = next;
		}
	}

	m->dirty = 0;
}

static int parser_run(parser *p, const char *src, int dump)
{
	p->srcptr = (char*)src;

	if (!parser_tokenize(p, 0, 0))
		return 0;

	if (p->skip) {
		p->m->status = 1;
		return 1;
	}

	if (!parser_attach(p, 0))
		return 0;

	if (p->command) {
		parser_dcg_rewrite(p);
		parser_assign_vars(p);
	}

	if (!parser_xref(p, p->t, NULL))
		return 0;

	query *q = create_query(p->m, 0);
	query_execute(q, p->t);

	if (q->halt)
		q->error = 0;
	else if (dump)
		dump_vars(q, p);

	p->m->halt = q->halt;
	p->m->halt_code = q->halt_code;
	p->m->status = q->status;

	if (!p->m->quiet && !p->directive && dump && q->m->stats) {
		fprintf(stderr,
			"Goals %llu, Matches %llu, Max frames %u, Max choices %u, Max trails: %u, Heap: %u, Backtracks %llu, TCOs:%llu\n",
			(unsigned long long)q->tot_goals, (unsigned long long)q->tot_matches,
			q->max_frames, q->max_choices, q->max_trails, q->max_heaps,
			(unsigned long long)q->tot_retries, (unsigned long long)q->tot_tcos);
	}

	int ok = !q->error;
	destroy_query(q);
	module_purge(p->m);
	return ok;
}

static int module_load_text(module *m, const char *src)
{
	parser *p = create_parser(m);
	p->consulting = 1;
	p->srcptr = (char*)src;
	int ok = parser_tokenize(p, 0, 0);

	if (!p->error && !p->end_of_term && p->t->cidx) {
		fprintf(stderr, "Error: incomplete statement\n");
		p->error = 1;
	}

	if (!p->error) {
		parser_xref_db(p);
		int save = p->m->quiet;
		p->m->quiet = 1;
		p->directive = 1;

		if (parser_run(p, "initialization(G), call(G)", 0))
			p->m->halt = 1;
		else
			p->m->halt = 0;

		p->directive = 0;
		p->m->quiet = save;
	}

	ok = !p->error;
	int halt = p->m->halt;
	destroy_parser(p);
	return ok && !halt;
}

int module_load_fp(module *m, FILE *fp)
{
	parser *p = create_parser(m);
	p->consulting = 1;
	p->fp = fp;
	int ok;

	do {
		if (getline(&p->save_line, &p->n_line, p->fp) == -1)
			break;

		p->srcptr = p->save_line;
		ok = parser_tokenize(p, 0, 0);
	}
	 while (ok);

	free(p->save_line);

	if (!p->error && !p->end_of_term && p->t->cidx) {
		fprintf(stderr, "Error: incomplete statement\n");
		p->error = 1;
	}

	if (!p->error) {
		parser_xref_db(p);
		int save = p->m->quiet;
		p->m->quiet = 1;
		p->directive = 1;

		if (parser_run(p, "initialization(G), call(G)", 0))
			p->m->halt = 1;
		else
			p->m->halt = 0;

		p->directive = 0;
		p->m->quiet = save;
	}

	ok = !p->error;
	int halt = p->m->halt;
	destroy_parser(p);
	return ok && !halt;
}

int module_load_file(module *m, const char *filename)
{
	if (!strcmp(filename, "user")) {
		for (int i = 0; i < MAX_STREAMS; i++) {
			stream *str = &g_streams[i];

			if (!strcmp(str->name, "user_input")) {
				int ok = module_load_fp(m, str->fp);
				clearerr(str->fp);
				return ok;
			}
		}
	}

	char tmpbuf[1024];
	strncpy(tmpbuf, filename, sizeof(tmpbuf)); tmpbuf[sizeof(tmpbuf)-1] = '\0';

	FILE *fp = fopen(tmpbuf, "r");

	if (!fp) {
		strncpy(tmpbuf, filename, sizeof(tmpbuf)); tmpbuf[sizeof(tmpbuf)-1] = '\0';
		strcat(tmpbuf, ".pro");
		fp = fopen(tmpbuf, "r");
	}

	if (!fp) {
		strncpy(tmpbuf, filename, sizeof(tmpbuf)); tmpbuf[sizeof(tmpbuf)-1] = '\0';
		strcat(tmpbuf, ".pl");
		fp = fopen(tmpbuf, "r");
	}

	if (!fp) {
		strncpy(tmpbuf, filename, sizeof(tmpbuf)); tmpbuf[sizeof(tmpbuf)-1] = '\0';
		fprintf(stderr, "Error: file '%s[.pro|.pl]' does not exist\n", filename);
		return 0;
	}

	free(m->filename);
	m->filename = strdup(filename);
	int ok = module_load_fp(m, fp);
	fclose(fp);

	return ok;
}

static void module_save_fp(module *m, FILE *fp, int canonical, int dq)
{
	query q = {0};
	q.m = m;

	for (rule *h = m->head; h; h = h->next) {
		if (h->flags&(FLAG_RULE_PREBUILT|FLAG_RULE_VOLATILE))
			continue;

		for (clause *r = h->head; r; r = r->next) {
			if (r->t.deleted)
				continue;

			if (canonical)
				write_canonical(&q, fp, r->t.cells, 0, dq, 0);
			else
				write_term(&q, fp, r->t.cells, 0, dq, 0, 0, 0);

			fprintf(fp, "\n");
		}
	}
}

int module_save_file(module *m, const char *filename)
{
	FILE *fp = fopen(filename, "w");

	if (!fp) {
		fprintf(stderr, "Error: file '%s' does not exist\n", filename);
		return 0;
	}

	module_save_fp(m, fp, 0, 0);
	fclose(fp);
	return 1;
}

static void make_rule(module *m, const char *src)
{
	m->prebuilt = 1;
	parser *p = create_parser(m);
	p->consulting = 1;
	p->srcptr = (char*)src;
	parser_tokenize(p, 0, 0);
	m->prebuilt = 0;
	destroy_parser(p);
}

module *create_module(const char *name)
{
	module *m = calloc(1, sizeof(module));
	m->name = strdup(name);
	m->next = g_modules;
	g_modules = m;

	m->p = create_parser(m);
	m->flag.double_quote_codes = 1;
	m->flag.character_escapes = 1;
	m->flag.rational_syntax_natural = 0;
	m->flag.prefer_rationals = 0;
	m->user_ops = MAX_USER_OPS;
	m->iso_only = 0;

	make_rule(m, "A -> B :- A, !, B.");
	make_rule(m, "phrase(P,L) :- phrase(P,L,[]).");
	make_rule(m, "phrase(P,L,Rest) :- call(P,L,Rest).");

	// This is an approximation...
	make_rule(m, "setup_call_cleanup(A,G,B) :- once(A), (G -> true ; (B, !, fail)).");

	// Edinburgh

	make_rule(m, "tab(0) :- !.");
	make_rule(m, "tab(N) :- put_code(32), M is N-1, tab(M).");
	make_rule(m, "tab(_,0) :- !.");
	make_rule(m, "tab(S,N) :- put_code(S,32), M is N-1, tab(S,M).");
	make_rule(m, "get0(C) :- get_code(C).");
	make_rule(m, "get0(S,C) :- get_code(S,C).");
	make_rule(m, "display(T) :- write_canonical(T).");
	make_rule(m, "display(S,T) :- write_canonical(S,T).");
	make_rule(m, "put(C) :- put_code(C).");
	make_rule(m, "put(S,C) :- put_code(S,C).");
	make_rule(m, "see(F) :- open(F,read,S), set_input(S).");
	make_rule(m, "tell(F) :- open(F,write,S), set_output(S).");
	make_rule(m, "append(F) :- open(F,append,S), set_output(S).");

	// SWI

	make_rule(m, "current_key(K) :- var(K), clause('$record_key'(K,_),_).");
	make_rule(m, "recorda(K,V) :- nonvar(K), nonvar(V), asserta('$record_key'(K,V)).");
	make_rule(m, "recordz(K,V) :- nonvar(K), nonvar(V), assertz('$record_key'(K,V)).");
	make_rule(m, "recorded(K,V) :- nonvar(K), clause('$record_key'(K,V),_).");

	make_rule(m, "recorda(K,V,R) :- nonvar(K), nonvar(V), asserta('$record_key'(K,V),R).");
	make_rule(m, "recordz(K,V,R) :- nonvar(K), nonvar(V), assertz('$record_key'(K,V),R).");
	make_rule(m, "recorded(K,V,R) :- nonvar(K), clause('$record_key'(K,V),_,R).");

	make_rule(m, "succ(X,Y) :- integer(X), Y is X + 1, X >= 0, !.");
	make_rule(m, "succ(X,Y) :- integer(Y), X is Y - 1, X >= 0.");

	// Other

	make_rule(m, "client(U,H,P,S) :- client(U,H,P,S,[]).");
	make_rule(m, "server(H,S) :- server(H,S,[]).");

	parser *p = create_parser(m);
	p->consulting = 1;
	parser_xref_db(p);
	destroy_parser(p);
	return m;
}

void destroy_module(module *m)
{
	while (m->tasks) {
		query *task = m->tasks->next;
		destroy_query(m->tasks);
		m->tasks = task;
	}

	for (rule *h = m->head; h != NULL;) {
		rule *save = h->next;

		for (clause *r = h->head; r != NULL;) {
			clause *save = r->next;
			clear_term(&r->t);
			free(r);
			r = save;
		}

		if (h->index)
			sl_destroy(h->index);

		free(h);
		h = save;
	}

	module *last = NULL;

	for (module *tmp = g_modules; tmp; tmp = tmp->next) {
		if (!strcmp(tmp->name, m->name)) {
			if (last)
				last->next = m->next;
			else
				g_modules = m->next;

			break;
		} else
			last = tmp;
	}

	if (m->fp)
		fclose(m->fp);

	free(m->filename);
	destroy_parser(m->p);
	free(m->name);
	free(m);
}

int deconsult(const char *filename)
{
	module *m = find_module(filename);
	if (!m) return 0;
	destroy_module(m);
	return 1;
}

int get_halt(prolog *pl) { return pl->m->halt; }
int get_halt_code(prolog *pl) { return pl->m->halt_code; }
int get_status(prolog *pl) { return pl->m->status; }

void set_trace(prolog *pl) { pl->m->trace = 1; }
void set_quiet(prolog *pl) { pl->m->quiet = 1; }
void set_stats(prolog *pl) { pl->m->stats = 1; }
void set_iso_only(prolog *pl) { pl->m->iso_only = 1; }
void set_opt(prolog *pl, int level) { pl->m->opt = level; }

int pl_eval(prolog *pl, const char *src)
{
	parser *p = create_parser(pl->m);
	p->command = 1;
	int ok = parser_run(p, src, 1);
	destroy_parser(p);
	return ok;
}

int pl_consult_fp(prolog *pl, FILE *fp)
{
	return module_load_fp(pl->m, fp);
}

int pl_consult(prolog *pl, const char *filename)
{
	return module_load_file(pl->m, filename);
}

prolog *pl_create()
{
	g_tpl_count++;
	srandom(time(0)+clock()+getpid());
	prolog *pl = calloc(1, sizeof(prolog));

	if (!g_pool) {
		g_pool = calloc(g_pool_size=INITIAL_POOL_SIZE, 1);
		g_pool_offset = 0;
	}

	g_empty_s = find_in_pool("");
	g_anon_s = find_in_pool("_");
	g_dot_s = find_in_pool(".");
	g_cut_s = find_in_pool("!");
	g_nil_s = find_in_pool("[]");
	g_true_s = find_in_pool("true");
	g_fail_s = find_in_pool("fail");
	g_clause_s = find_in_pool(":-");
	g_sys_elapsed_s = find_in_pool("sys_elapsed");
	g_sys_queue_s = find_in_pool("sys_queue");
	g_eof_s = find_in_pool("end_of_file");
	g_lt_s = find_in_pool("<");
	g_gt_s = find_in_pool(">");
	g_eq_s = find_in_pool("=");

	g_streams[0].fp = stdin;
	g_streams[0].filename = strdup("stdin");
	g_streams[0].name = strdup("user_input");
	g_streams[0].mode = strdup("read");

	g_streams[1].fp = stdout;
	g_streams[1].filename = strdup("stdout");
	g_streams[1].name = strdup("user_output");
	g_streams[1].mode = strdup("append");

	g_streams[2].fp = stderr;
	g_streams[2].filename = strdup("stderr");
	g_streams[2].name = strdup("user_error");
	g_streams[2].mode = strdup("append");

	pl->m = create_module("user");
	pl->m->filename = strdup("~/.tpl_user");
	library *lib = g_libs;

	while (lib->name) {
		if (!strcmp(lib->name, "apply") || !strcmp(lib->name, "dict") ||
			!strcmp(lib->name, "http") || !strcmp(lib->name, "lists")) {
			char *src = strndup((const char*)lib->start, (lib->end - lib->start));
			module_load_text(pl->m, src);
			free(src);
		}

		lib++;
	}

	if (isatty(0)) {
		load_keywords(pl->m);
		history_keywords((const char **)pl->m->keywords);
	}

	return pl;
}

void pl_destroy(prolog *pl)
{
	destroy_module(pl->m);
	free(pl);

	if (!--g_tpl_count) {
		for (int i = 0; i < MAX_STREAMS; i++) {
			if (g_streams[i].fp) {
				if (i > 2)
					fclose(g_streams[i].fp);

				free(g_streams[i].filename);
				free(g_streams[i].mode);

				free(g_streams[i].name);
				g_streams[i].name = NULL;
			}
		}

		memset(g_streams, 0, sizeof(g_streams));

		while (g_modules) {
			module *m = g_modules;
			g_modules = m->next;
			destroy_module(m);
		}

		free(g_pool);
		g_pool = NULL;
	}
}

