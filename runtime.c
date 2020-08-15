#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

#ifdef _WIN32
#include <io.h>
#define isatty _isatty
#else
#include <unistd.h>
#endif

#include "internal.h"

#define trace if (q->trace /*&& !consulting*/) trace_call

int g_tpl_abort = 0;

enum { CALL, EXIT, REDO, NEXT, FAIL };

static void check_trail(query *q)
{
	if (q->st.tp > q->max_trails) {
		q->max_trails = q->st.tp;

		if (q->st.tp >= q->nbr_trails) {
			q->nbr_trails += q->nbr_trails / 2;

			if ((sizeof(trail)*q->nbr_trails) > (1024LL*1024*1024)) {
				fprintf(stderr, "Out of trail\n");
				abort();
			}

			q->trails = realloc(q->trails, sizeof(trail)*q->nbr_trails);
			assert(q->trails);
		}
	}
}

static void check_choice(query *q)
{
	if (q->cp > q->max_choices) {
		q->max_choices = q->cp;

		if (q->cp >= q->nbr_choices) {
			q->nbr_choices += q->nbr_choices / 2;

			if ((sizeof(choice)*q->nbr_choices) > (1024LL*1024*1024)) {
				fprintf(stderr, "Out of choices\n");
				abort();
			}

			q->choices = realloc(q->choices, sizeof(choice)*q->nbr_choices);
			assert(q->choices);
		}
	}
}

static void check_frame(query *q)
{
	if (q->st.fp > q->max_frames) {
		q->max_frames = q->st.fp;

		if (q->st.fp >= q->nbr_frames) {
			q->nbr_frames += q->nbr_frames / 2;

			if ((sizeof(frame)*q->nbr_frames) > (1024LL*1024*1024)) {
				fprintf(stderr, "Out of frames\n");
				abort();
			}

			assert(q->nbr_frames);
			q->frames = realloc(q->frames, sizeof(frame)*q->nbr_frames);
			assert(q->frames);
		}
	}
}

static void check_slot(query *q)
{
	if (q->st.sp > q->max_slots) {
		q->max_slots = q->st.sp;

		if ((q->st.sp+MAX_ARITY) >= q->nbr_slots) {
			idx_t save_slots = q->nbr_slots;
			q->nbr_slots += q->nbr_slots / 2;

			if ((sizeof(slot)*q->nbr_slots) > (1024LL*1024*1024)) {
				fprintf(stderr, "Out of environment\n");
				abort();
			}

			q->slots = realloc(q->slots, sizeof(slot)*q->nbr_slots);
			assert(q->slots);
			memset(q->slots+save_slots, 0, sizeof(slot)*(q->nbr_slots-save_slots));
		}
	}
}

unsigned create_vars(query *q, unsigned nbr)
{
	frame *g = GET_FRAME(q->st.curr_frame);

	if ((g->env + g->nbr_slots) == q->st.sp) {
		unsigned slot_nbr = g->nbr_vars;
		g->nbr_slots += nbr;
		g->nbr_vars += nbr;
		q->st.sp += nbr;
		return slot_nbr;
	}

	assert(!g->overflow);
	g->overflow = q->st.sp;
	q->st.sp += nbr;
	check_slot(q);

	for (int i = 0; i < nbr; i++) {
		slot *e = GET_SLOT(g, g->nbr_vars+i);
		e->c.val_type = TYPE_EMPTY;
	}

	unsigned slot_nbr = g->nbr_vars;
	g->nbr_vars += nbr;
	return slot_nbr;
}

static void trace_call(query *q, cell *c, int box)
{
	if (!c->fn)
		return;

	if (is_empty(c))
		return;

	fprintf(stderr, " [%lld] ", (long long)q->step);
	fprintf(stderr, "%s ", box==CALL?"CALL":box==EXIT?"EXIT":box==REDO?"REDO":box==NEXT?isatty(2)?"\e[32mNEXT\e[0m":"NEXT":isatty(2)?"\e[31mFAIL\e[0m":"FAIL");

#if DEBUG
	frame *g = GET_FRAME(q->st.curr_frame);
	fprintf(stderr, "{f(%u:%u):ch%u:tp%u:cp%u:fp%u:sp%u} ", q->st.curr_frame, g->nbr_vars, g->any_choices, q->st.tp, q->cp, q->st.fp, q->st.sp);
#endif

	idx_t save_ctx = q->latest_ctx;
	q->latest_ctx = q->st.curr_frame;
	write_term(q, stderr, c, -1, 0, 0, 100, 0);
	q->latest_ctx = save_ctx;
	fprintf(stderr, "\n");
}

static void unwind_trail(query *q, const choice *ch)
{
	while (q->st.tp > ch->st.tp) {
		trail *tr = q->trails + --q->st.tp;

		if (ch->pins) {
			if (ch->pins & (1 << tr->slot_nbr))
				continue;
		}

		frame *g = GET_FRAME(tr->ctx);
		slot *e = GET_SLOT(g, tr->slot_nbr);
		e->c.val_type = TYPE_EMPTY;
	}
}

void undo_me(query *q)
{
	idx_t curr_choice = q->cp - 1;
	const choice *ch = q->choices + curr_choice;
	unwind_trail(q, ch);
}

void try_me(const query *q, unsigned vars)
{
	frame *g = GET_FRAME(q->st.fp);
	g->nbr_slots = vars;
	g->env = q->st.sp;
	slot *e = GET_SLOT(g, 0);

	for (unsigned i = 0; i < vars; i++, e++)
		e->c.val_type = TYPE_EMPTY;
}

void make_choice(query *q)
{
	check_frame(q);
	check_slot(q);
	check_choice(q);

	idx_t curr_choice = q->cp++;
	choice *ch = q->choices + curr_choice;
	ch->st = q->st;
	ch->qnbr = 0;
	ch->inner_cut = 0;
	ch->catchme = 0;
	ch->pins = 0;

	q->st.iter = NULL;

	frame *g = GET_FRAME(q->st.curr_frame);
	ch->nbr_vars = g->nbr_vars;
	ch->any_choices = g->any_choices;
}

int retry_choice(query *q)
{
	if (!q->cp)
		return 0;

	idx_t curr_choice = drop_choice(q);
	const choice *ch = q->choices + curr_choice;
	unwind_trail(q, ch);

	if (ch->catchme == 2)
		return retry_choice(q);

	for (idx_t i = ch->st.hp; i < q->st.hp; i++) {
		cell *c = &q->arenas->heap[i];

		if (is_bigstring(c) && !is_const(c)) {
			free(c->val_str);
		} else if (is_integer(c) && ((c)->flags&FLAG_STREAM)) {
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

		c->val_type = TYPE_EMPTY;
	}

	for (arena *a = q->arenas; a;) {
		if (a->nbr > ch->st.anbr) {
			arena *save = a;
			q->arenas = a = a->next;
			free(save->heap);
			free(save);
			continue;
		}

		if (a->nbr == ch->st.anbr)
			break;

		a = a->next;
	}

	q->st = ch->st;

	frame *g = GET_FRAME(q->st.curr_frame);
	g->nbr_vars = ch->nbr_vars;
	g->any_choices = ch->any_choices;
	g->overflow = 0;
	return 1;
}

idx_t drop_choice(query *q)
{
	idx_t curr_choice = --q->cp;
	return curr_choice;
}

static void make_frame(query *q, unsigned nbr_vars, int last_match)
{
	frame *g = GET_FRAME(q->st.curr_frame);

	if (!last_match)
		g->any_choices = 1;

	idx_t new_frame = q->st.fp++;
	g = GET_FRAME(new_frame);
	g->prev_frame = q->st.curr_frame;
	g->curr_cell = q->st.curr_cell;
	g->nbr_slots = nbr_vars;
	g->nbr_vars = nbr_vars;
	g->any_choices = 0;
	q->st.sp += nbr_vars;

	q->st.curr_frame = new_frame;
}

static void reuse_frame(query *q, unsigned nbr_vars)
{
	frame *g = GET_FRAME(q->st.curr_frame);
	g->any_choices = 0;
	g->overflow = 0;
	g->nbr_slots = nbr_vars;
	g->nbr_vars = nbr_vars;

	if (!q->no_tco && q->m->opt) {
		frame *new_g = GET_FRAME(q->st.fp);
		slot *from = GET_SLOT(new_g, 0);
		slot *to = GET_SLOT(g, 0);
		memcpy(to, from, sizeof(slot)*nbr_vars);
		q->st.sp = g->env + nbr_vars;
	} else {
		g->env = q->st.sp;
		q->st.sp += nbr_vars;
	}

	q->tot_tcos++;
}

static int check_slots(const query *q, frame *g, term *t)
{
	if (t && (g->nbr_vars != t->nbr_vars))
		return 0;

	for (unsigned i = 0; i < g->nbr_vars; i++) {
		slot *e = GET_SLOT(g, i);

		if (is_indirect(&e->c))
			return 0;
	}

	return 1;
}

static void commit_me(query *q, term *t)
{
	frame *g = GET_FRAME(q->st.curr_frame);
	int last_match = (!q->st.curr_clause->next && !q->st.iter) || t->first_cut;
	int recursive = last_match && (q->st.curr_cell->flags&FLAG_TAILREC);
	int tco = recursive && !g->any_choices && check_slots(q, g, t);

	if (!last_match) {
		idx_t curr_choice = q->cp - 1;
		choice *ch = q->choices + curr_choice;
		ch->st.curr_clause = q->st.curr_clause;
	} else
		drop_choice(q);

	if (tco)
		reuse_frame(q, t->nbr_vars);
	else
		make_frame(q, t->nbr_vars, last_match);

	if (t->cut_only)
		q->st.curr_cell = NULL;
	else
		q->st.curr_cell = get_body(q->m, t->cells);

	q->nv_mask = 0;
}

void cut_me(query *q, int inner_cut)
{
	frame *g = GET_FRAME(q->st.curr_frame);
	g->any_choices = 0;

	if (!q->cp) {
		q->st.tp = 0;
		return;
	}

	idx_t curr_choice = q->cp - 1;
	choice *ch = q->choices + curr_choice;
	int cut = 0;

	while ((ch->st.fp >= q->st.curr_frame) && !cut) {
		if (ch->qnbr) {
			q->qnbr = ch->qnbr;
			free(q->tmpq[q->qnbr]);
			q->tmpq[q->qnbr] = NULL;
			q->qnbr--;
		}

		if (ch->inner_cut && !inner_cut)
			break;

		if (ch->inner_cut && inner_cut)
			cut = 1;

		if (ch->st.iter) {
			sl_done(ch->st.iter);
			ch->st.iter = NULL;
		}

		q->cp--;
		ch--;

		if (!q->cp)
			break;
	}

	if (!q->cp) {
		q->st.tp = 0;
	}
}

static void follow_me(query *q)
{
	q->st.curr_cell += q->st.curr_cell->nbr_cells;

	while (q->st.curr_cell && is_end(q->st.curr_cell))
		q->st.curr_cell = q->st.curr_cell->val_cell;
}

static int resume_frame(query *q)
{
	if (!q->st.curr_frame)
		return 0;

	frame *g = GET_FRAME(q->st.curr_frame);

#if 0
	int det = check_slots(q, g, NULL);

	if (det && !g->any_choices && (q->st.curr_frame == (q->st.fp-1)) && q->m->opt)
		q->st.fp--;
#endif

	cell *curr_cell = g->curr_cell;
	g = GET_FRAME(q->st.curr_frame=g->prev_frame);
	q->st.curr_cell = curr_cell;
	return 1;
}

cell *deref_var(query *q, cell *c, idx_t c_ctx)
{
	frame *g = GET_FRAME(c_ctx);
	slot *e = GET_SLOT(g, c->slot_nbr);

	while (is_var(&e->c)) {
		c = &e->c;
		c_ctx = e->ctx;
		frame *g = GET_FRAME(c_ctx);
		e = GET_SLOT(g, c->slot_nbr);
	}

	if (is_empty(&e->c)) {
		q->latest_ctx = c_ctx;
		return c;
	}

	if (is_indirect(&e->c)) {
		q->latest_ctx = e->ctx;
		return e->c.val_cell;
	}

	q->latest_ctx = q->st.curr_frame;
	return &e->c;
}

static void make_indirect(cell *tmp, cell *c)
{
	tmp->val_type = TYPE_INDIRECT;
	tmp->nbr_cells = 1;
	tmp->arity = 0;
	tmp->val_cell = c;
}

void set_var(query *q, cell *c, idx_t c_ctx, cell *v, idx_t v_ctx)
{
	frame *g = GET_FRAME(c_ctx);
	slot *e = GET_SLOT(g, c->slot_nbr);
	e->ctx = v_ctx;

	if (v->arity)
		make_indirect(&e->c, v);
	else
		e->c = *v;

	if (!q->cp)
		return;

	check_trail(q);
	trail *tr = q->trails + q->st.tp++;
	tr->slot_nbr = c->slot_nbr;
	tr->ctx = c_ctx;
}

void reset_value(query *q, cell *c, idx_t c_ctx, cell *v, idx_t v_ctx)
{
	frame *g = GET_FRAME(c_ctx);
	slot *e = GET_SLOT(g, c->slot_nbr);

	while (is_var(&e->c)) {
		c = &e->c;
		c_ctx = e->ctx;
		g = GET_FRAME(c_ctx);
		e = GET_SLOT(g, c->slot_nbr);
	}

	e->ctx = v_ctx;

	if (v->arity)
		make_indirect(&e->c, v);
	else
		e->c = *v;
}

static int unify_structure(query *q, cell *p1, idx_t p1_ctx, cell *p2, idx_t p2_ctx)
{
	if (p1->arity != p2->arity)
		return 0;

	if (p1->val_offset != p2->val_offset)
		return 0;

	unsigned arity = p1->arity;
	p1++; p2++;

	while (arity--) {
		cell *c1 = GET_VALUE(q, p1, p1_ctx);
		idx_t c1_ctx = q->latest_ctx;
		cell *c2 = GET_VALUE(q, p2, p2_ctx);
		idx_t c2_ctx = q->latest_ctx;

		if (!unify(q, c1, c1_ctx, c2, c2_ctx))
			return 0;

		p1 += p1->nbr_cells;
		p2 += p2->nbr_cells;
	}

	return 1;
}

static int unify_rational(cell *p1, cell *p2)
{
	if (is_rational(p2))
		return (p1->val_num == p2->val_num) && (p1->val_den == p2->val_den);

	return 0;
}

static int unify_float(cell *p1, cell *p2)
{
	if (is_real(p2))
		return p1->val_real == p2->val_real;

	return 0;
}

#define GET_STR2(c) ((c)->flags&FLAG_SMALL_STRING ? (c)->val_chars : (c)->val_str)

static int unify_literal(cell *p1, cell *p2)
{
	if (is_literal(p2))
		return p1->val_offset == p2->val_offset;

	if (is_string(p2))
		return !strcmp(g_pool+p1->val_offset, GET_STR2(p2));

	return 0;
}

static int unify_string(cell *p1, cell *p2)
{
	if (is_literal(p2))
		return !strcmp(GET_STR2(p1), g_pool+p2->val_offset);

	if (is_string(p2))
		return !strcmp(GET_STR2(p1), GET_STR2(p2));

	return 0;
}

struct dispatch {
	uint8_t val_type;
	int (*fn)(cell *p1, cell *p2);
};

static const struct dispatch g_disp[] =
{
	{TYPE_EMPTY, NULL},
	{TYPE_VAR, NULL},
	{TYPE_LITERAL, unify_literal},
	{TYPE_STRING, unify_string},
	{TYPE_INT, unify_rational},
	{TYPE_FLOAT, unify_float},
	{0}
};

int unify(query *q, cell *p1, idx_t p1_ctx, cell *p2, idx_t p2_ctx)
{
	if (is_var(p1) && is_var(p2)) {
		if (p2_ctx > p1_ctx)
			set_var(q, p2, p2_ctx, p1, p1_ctx);
		else if (p2_ctx < p1_ctx)
			set_var(q, p1, p1_ctx, p2, p2_ctx);
		else if (p1->slot_nbr != p2->slot_nbr)
			set_var(q, p1, p1_ctx, p2, p2_ctx);

		return 1;
	}

	if (is_var(p1)) {
		if (is_empty(p2))
			return 1;

		if (is_structure(p2) && (p2_ctx >= q->st.curr_frame))
			q->no_tco = 1;

		set_var(q, p1, p1_ctx, p2, p2_ctx);
		return 1;
	}

	if (is_var(p2)) {
		if (is_empty(p1))
			return 1;

		if (is_structure(p1) && (p1_ctx >= q->st.curr_frame))
			q->no_tco = 1;

		set_var(q, p2, p2_ctx, p1, p1_ctx);
		return 1;
	}

	if (p1->arity)
		return unify_structure(q, p1, p1_ctx, p2, p2_ctx);

	return g_disp[p1->val_type].fn(p1, p2);
}

static void next_key(query *q)
{
	if (q->st.iter) {
		if (!sl_nextkey(q->st.iter, (void**)&q->st.curr_clause)) {
			q->st.curr_clause = NULL;
			q->st.iter = NULL;
		}
	} else
		q->st.curr_clause = q->st.curr_clause->next;
}

static int do_match2(query *q, cell *curr_cell)
{
	cell *head = get_head(q->m, curr_cell);
	rule *h = find_match(q->m, head);

	if (!h)
		q->st.curr_clause = NULL;
	else
		q->st.curr_clause = h->head;

	make_choice(q);

	for (; q->st.curr_clause; q->st.curr_clause = q->st.curr_clause->next) {
		if (q->st.curr_clause->t.deleted)
			continue;

		term *t = &q->st.curr_clause->t;
		cell *c = t->cells;
		try_me(q, t->nbr_vars);
		q->tot_matches++;

		if (unify_structure(q, curr_cell, q->st.curr_frame, c, q->st.fp))
			return 1;

		undo_me(q);
	}

	drop_choice(q);
	return 0;
}

int do_match(query *q, cell *curr_cell)
{
	if (q->retry)
		q->st.curr_clause = q->st.curr_clause->next;
	else {
		if (!strcmp(GET_STR(curr_cell), ":-"))
			return do_match2(q, curr_cell);

		rule *h = find_match(q->m, curr_cell);

		if (!h)
			q->st.curr_clause = NULL;
		else
			q->st.curr_clause = h->head;
	}

	make_choice(q);

	for (; q->st.curr_clause; q->st.curr_clause = q->st.curr_clause->next) {
		if (q->st.curr_clause->t.deleted)
			continue;

		term *t = &q->st.curr_clause->t;
		cell *head = get_head(q->m, t->cells);
		try_me(q, t->nbr_vars);
		q->tot_matches++;

		if (unify_structure(q, curr_cell, q->st.curr_frame, head, q->st.fp))
			return 1;

		undo_me(q);
	}

	drop_choice(q);
	return 0;
}

static int match(query *q)
{
	if (!q->retry) {
		rule *h = q->st.curr_cell->match;

		if (!h) {
			q->st.curr_cell->match = find_match(q->m, q->st.curr_cell);
			h = q->st.curr_cell->match;

			if (!h) {
				if (!is_end(q->st.curr_cell) &&
					!(is_literal(q->st.curr_cell) && !strcmp(GET_STR(q->st.curr_cell), "initialization")))
					throw_error(q, q->st.curr_cell, "existence_error", "procedure");
				else
					q->error = 1;

				return 0;
			}
		}

		if (h->index) {
			cell *key = deep_clone_term_on_heap(q, q->st.curr_cell, q->st.curr_frame);
			q->st.iter = sl_findkey(h->index, key);
			next_key(q);
		} else {
			q->st.curr_clause = h->head;
			q->st.iter = NULL;
		}
	} else
		next_key(q);

	if (!q->st.curr_clause)
		return 0;

	make_choice(q);

	for (; q->st.curr_clause; next_key(q)) {
		if (q->st.curr_clause->t.deleted)
			continue;

		term *t = &q->st.curr_clause->t;
		cell *head = get_head(q->m, t->cells);
		try_me(q, t->nbr_vars);
		q->tot_matches++;
		q->no_tco = 0;

		if (unify_structure(q, q->st.curr_cell, q->st.curr_frame, head, q->st.fp)) {
			trace(q, q->st.curr_cell, EXIT);
			commit_me(q, t);
			return 1;
		}

		undo_me(q);
	}

	drop_choice(q);
	return 0;
}

void run_query(query *q)
{
	q->yielded = 0;

	while (!g_tpl_abort && !q->error) {
		if (q->retry) {
			if (!retry_choice(q))
				break;
		}

		if (is_var(q->st.curr_cell)) {
			cell *c = GET_VALUE(q, q->st.curr_cell, q->st.curr_frame);

			if (!call_me(q, c, q->latest_ctx))
				continue;
		}

		q->tot_goals++;
		q->step++;
		trace(q, q->st.curr_cell, q->retry?REDO:q->resume?NEXT:CALL);

		if (!(q->st.curr_cell->flags&FLAG_BUILTIN)) {
			if (!is_literal(q->st.curr_cell)) {
				throw_error(q, q->st.curr_cell, "type_error", "callable");
				break;
			}

			if (!match(q)) {
				q->retry = 1;
				q->tot_retries++;
				trace(q, q->st.curr_cell, FAIL);
				continue;
			}
		} else {
			if (!q->st.curr_cell->fn) {
				q->tot_goals--;
				q->step--;
				q->st.curr_cell++;					// NO-OP
				continue;
			}

			if (!q->st.curr_cell->fn(q)) {
				q->retry = 1;

				if (q->yielded)
					break;

				q->tot_retries++;
				trace(q, q->st.curr_cell, FAIL);
				continue;
			}

			trace(q, q->st.curr_cell, EXIT);
			follow_me(q);
		}

		q->resume = 0;
		q->retry = 0;

		while (!q->st.curr_cell || is_end(q->st.curr_cell)) {
			if (!resume_frame(q)) {
				q->status = 1;
				return;
			}

			q->resume = 1;
			follow_me(q);
		}
	}
}

void query_execute(query *q, term *t)
{
	q->st.curr_cell = t->cells;
	q->st.sp = t->nbr_vars;
	q->st.curr_frame = 0;
	q->st.fp = 1;

	frame *g = q->frames + q->st.curr_frame;
	g->nbr_vars = t->nbr_vars;
	g->nbr_slots = t->nbr_vars;
	run_query(q);
}

