#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <ctype.h>
#include <errno.h>

#include "internal.h"

#define GET_RAW_ARG(n,p) \
	__attribute__((unused)) cell *p = get_raw_arg(q,n); \
	__attribute__((unused)) idx_t p##_ctx = q->latest_ctx

extern int do_yield_0(query *q);

#define is_atomic(c) (is_atom(c) || is_number(c))
#define is_callable(c) (is_literal(c) || is_string(c))
#define is_list_or_nil(c) (is_list(c) || is_nil(c))
#define is_list_or_nil_or_var(c) (is_list_or_nil(c) || is_var(c))
#define is_list_or_var(c) (is_list(c) || is_var(c))
#define is_structure_or_var(c) (is_structure(c) || is_var(c))
#define is_atom_or_var(c) (is_atom(c) || is_var(c))
#define is_atom_or_int(c) (is_atom(c) || is_integer(c))
#define is_integer_or_var(c) (is_integer(c) || is_var(c))
#define is_integer_or_atom(c) (is_integer(c) || is_atom(c))
#define is_nonvar(c) (!is_var(c))
#define is_stream(c) (get_stream(q,c) >= 0)
#define is_stream_or_structure(c) (is_structure(c) || is_stream(c))
#define is_any(c) 1

#define GET_FIRST_ARG(p,val_type) \
	__attribute__((unused)) cell *p = get_first_arg(q); \
	__attribute__((unused)) idx_t p##_ctx = q->latest_ctx; \
	if (!is_##val_type(p)) { throw_error(q, p, "type_error", #val_type); return 0; }

#define GET_NEXT_ARG(p,val_type) \
	__attribute__((unused)) cell *p = get_next_arg(q); \
	__attribute__((unused)) idx_t p##_ctx = q->latest_ctx; \
	if (!is_##val_type(p)) { throw_error(q, p, "type_error", #val_type); return 0; }

inline static cell *get_first_arg(query *q)
{
	q->last_arg = q->st.curr_cell + 1;
	return GET_VALUE(q, q->last_arg, q->st.curr_frame);
}

inline static cell *get_next_arg(query *q)
{
	q->last_arg += q->last_arg->nbr_cells;
	return GET_VALUE(q, q->last_arg, q->st.curr_frame);
}

inline static cell *get_next_raw_arg(query *q)
{
	q->last_arg += q->last_arg->nbr_cells;
	return q->last_arg;
}

inline static cell *get_raw_arg(query *q, int n)
{
	cell *c = q->st.curr_cell + 1;

	for (int i = 1; i < n; i++)
		c += c->nbr_cells;

	return c;
}
