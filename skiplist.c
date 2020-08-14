#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <math.h>

#include "skiplist.h"

typedef struct keyval_ keyval_t;
typedef struct slnode_ slnode_t;

struct keyval_ {
	void *key;
	void *val;
};

#define BUCKET_SIZE 16

struct slnode_ {
	keyval_t bkt[BUCKET_SIZE];
	int nbr;
	slnode_t *forward[];
};

struct sliter_ {
	skiplist *l;
	slnode_t *p;
	const void *key;
	int idx, dynamic;
};

struct skiplist_ {
	slnode_t *header;
	int (*compkey)(const void*, const void*);
	sliter iter;
	size_t count;
	int level, iter_cnt;
	unsigned seed;
};

#define max_levels 32
#define max_level (max_levels - 1)
#define new_node_of_level(x) (slnode_t*)malloc(sizeof(slnode_t) + ((x) * sizeof(slnode_t*)))

skiplist *sl_create(int (*compkey)(const void*, const void*))
{
	skiplist *l = (skiplist*)malloc(sizeof(struct skiplist_));
	l->header = new_node_of_level(max_levels);
	l->seed = (unsigned)(size_t)(l + clock());
	l->level = 1;

	for (int i = 0; i < max_levels; i++)
		l->header->forward[i] = NULL;

	l->header->nbr = 1;
	l->header->bkt[0].key = NULL;
	l->compkey = compkey;
	l->iter_cnt = 0;
	l->count = 0;
	return l;
}

void sl_destroy(skiplist *l)
{
	slnode_t *p, *q;
	p = l->header;
	q = p->forward[0];
	free(p);
	p = q;

	while (p) {
		q = p->forward[0];
		free(p);
		p = q;
	}

	free(l);
}

size_t sl_count(const skiplist *l) { return l->count; }

static int binary_search(const skiplist *l, const keyval_t n[], const void *key, int imin, int imax)
{
	while (imax >= imin) {
		int imid = (imax + imin) / 2;

		if (l->compkey(n[imid].key, key) == 0)
			return imid;
		else if (l->compkey(n[imid].key, key) < 0)
			imin = imid + 1;
		else
			imax = imid - 1;
	}

	return -1;
}

// Modified binary search: return position where it is or ought to be

static int binary_search1(const skiplist *l, const keyval_t n[], const void *key, int imin, int imax)
{
	int imid = 0;

	while (imax >= imin) {
		imid = (imax + imin) / 2;

		if (l->compkey(n[imid].key, key) < 0)
			imin = imid + 1;
		else
			imax = imid - 1;
	}

	if (l->compkey(n[imid].key, key) < 0)
		imid++;

	return imid;
}

// Modified binary search: return position where it is or ought to be

static int binary_search2(const skiplist *l, const keyval_t n[], const void *key, int imin, int imax)
{
	int imid = 0;

	while (imax >= imin) {
		imid = (imax + imin) / 2;

		if (l->compkey(n[imid].key, key) <= 0)
			imin = imid + 1;
		else
			imax = imid - 1;
	}

	if (l->compkey(n[imid].key, key) <= 0)
		imid++;

	return imid;
}

#define frand(seedp) ((double)rand_r(seedp) / RAND_MAX)

static int random_level(unsigned *seedp)
{
	const double P = 0.5;
	int lvl = (int)(log(frand(seedp)) / log(1. - P));
	return lvl < max_level ? lvl : max_level;
}

int sl_set(skiplist *l, const void *key, const void *val)
{
	slnode_t *update[max_levels];
	slnode_t *p, *q;
	slnode_t stash;
	stash.nbr = 0;
	int k;
	p = l->header;

	for (int k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[0].key, key) < 0))
			p = q;

		update[k] = p;
	}

	if (p != l->header) {
		int imid = binary_search2(l, p->bkt, key, 0, p->nbr - 1);

		if (p->nbr < BUCKET_SIZE) {
			int j;

			for (j = p->nbr; j > imid; j--)
				p->bkt[j] = p->bkt[j - 1];

			p->bkt[j].key = (void*)key;
			p->bkt[j].val = (void*)val;
			p->nbr++;
			l->count++;
			return 1;
		}

		// Don't drop this unless you are 100% sure:

		while ((imid < p->nbr) && (l->compkey(p->bkt[imid].key, key) == 0))
			imid++;

		if (imid <= BUCKET_SIZE) {
			for (int j = imid; j < p->nbr; j++)
				stash.bkt[stash.nbr++] = p->bkt[j];

			p->nbr = imid;
		}
	}

	k = random_level(&l->seed);

	if (k >= l->level) {
		l->level++;
		k = l->level - 1;
		update[k] = l->header;
	}

	q = new_node_of_level(k + 1);
	q->bkt[0].key = (void*)key;
	q->bkt[0].val = (void*)val;
	q->nbr = 1;
	l->count++;

	if (stash.nbr) {
		for (int i = 0; i < stash.nbr; i++, q->nbr++)
			q->bkt[q->nbr] = stash.bkt[i];
	}

	for (; k >= 0; k--) {
		p = update[k];
		q->forward[k] = p->forward[k];
		p->forward[k] = q;
	}

	return 1;
}

int sl_app(skiplist *l, const void *key, const void *val)
{
	slnode_t *update[max_levels];
	slnode_t *p, *q;
	slnode_t stash;
	stash.nbr = 0;
	int k;
	p = l->header;

	for (int k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[0].key, key) <= 0))
			p = q;

		update[k] = p;
	}

	if (p != l->header) {
		int imid = binary_search2(l, p->bkt, key, 0, p->nbr - 1);

		if (p->nbr < BUCKET_SIZE) {
			int j;

			for (j = p->nbr; j > imid; j--)
				p->bkt[j] = p->bkt[j - 1];

			p->bkt[j].key = (void*)key;
			p->bkt[j].val = (void*)val;
			p->nbr++;
			l->count++;
			return 1;
		}

		// Don't drop this unless you are 100% sure:

		while ((imid < p->nbr) && (l->compkey(p->bkt[imid].key, key) == 0))
			imid++;

		if (imid <= BUCKET_SIZE) {
			for (int j = imid; j < p->nbr; j++)
				stash.bkt[stash.nbr++] = p->bkt[j];

			p->nbr = imid;
		}
	}

	k = random_level(&l->seed);

	if (k >= l->level) {
		l->level++;
		k = l->level - 1;
		update[k] = l->header;
	}

	q = new_node_of_level(k + 1);
	q->bkt[0].key = (void*)key;
	q->bkt[0].val = (void*)val;
	q->nbr = 1;
	l->count++;

	if (stash.nbr) {
		for (int i = 0; i < stash.nbr; i++, q->nbr++)
			q->bkt[q->nbr] = stash.bkt[i];
	}

	for (; k >= 0; k--) {
		p = update[k];
		q->forward[k] = p->forward[k];
		p->forward[k] = q;
	}

	return 1;
}

int sl_get(const skiplist *l, const void *key, const void **val)
{
	int k;
	slnode_t *p, *q = 0;
	p = l->header;

	for (k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[q->nbr - 1].key, key) < 0))
			p = q;
	}

	if (!(q = p->forward[0]))
		return 0;

	int imid = binary_search(l, q->bkt, key, 0, q->nbr - 1);

	if (imid < 0)
		return 0;

	*val = q->bkt[imid].val;
	return 1;
}

int sl_del(skiplist *l, const void *key)
{
	int k, m;
	slnode_t *update[max_levels];
	slnode_t *p, *q;
	p = l->header;

	for (k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[q->nbr - 1].key, key) < 0))
			p = q;

		update[k] = p;
	}

	if (!(q = p->forward[0]))
		return 0;

	int imid = binary_search(l, q->bkt, key, 0, q->nbr - 1);

	if (imid < 0)
		return 0;

	while (imid < (q->nbr - 1)) {
		q->bkt[imid] = q->bkt[imid + 1];
		imid++;
	}

	q->nbr--;
	l->count--;

	if (q->nbr)
		return 1;

	m = l->level - 1;

	for (k = 0; k <= m; k++) {
		p = update[k];

		if (!p || (p->forward[k] != q))
			break;

		p->forward[k] = q->forward[k];
	}

	free(q);
	m = l->level - 1;

	while (!l->header->forward[m] && (m > 0))
		m--;

	l->level = m + 1;
	return 1;
}

void sl_iterate(const skiplist *l, int (*f)(void*, const void*, const void*), void *p1)
{
	slnode_t *p;
	p = l->header;
	p = p->forward[0];

	while (p) {
		slnode_t *q = p->forward[0];

		for (int j = 0; j < p->nbr; j++) {
			if (!f(p1, p->bkt[j].key, p->bkt[j].val))
				return;
		}

		p = q;
	}
}

void sl_find(const skiplist *l, const void *key, int (*f)(void*, const void*, const void*), void *p1)
{
	slnode_t *p, *q = 0;
	p = l->header;

	for (int k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[q->nbr - 1].key, key) < 0))
			p = q;
	}

	if (!(q = p->forward[0]))
		return;

	int imid = binary_search2(l, q->bkt, key, 0, q->nbr - 1);

	if (imid < 0)
		return;

	p = q;

	for (int j = imid; j < p->nbr; j++) {
		if (!f(p1, p->bkt[j].key, p->bkt[j].val))
			return;
	}

	while (p) {
		slnode_t *q = p->forward[0];

		for (int j = 0; j < p->nbr; j++) {
			if (!f(p1, p->bkt[j].key, p->bkt[j].val))
				return;
		}

		p = q;
	}
}

sliter *sl_findkey(skiplist *l, const void *key)
{
	slnode_t *p, *q = 0;
	p = l->header;

	for (int k = l->level - 1; k >= 0; k--) {
		while ((q = p->forward[k]) && (l->compkey(q->bkt[q->nbr - 1].key, key) < 0))
			p = q;
	}

	if (!(q = p->forward[0]))
		return NULL;

	int imid = binary_search1(l, q->bkt, key, 0, q->nbr - 1);

	if (imid < 0)
		return NULL;

	if (l->compkey(q->bkt[imid].key, key) != 0)
		return NULL;

	sliter *iter;

	if (l->iter_cnt++) {
		iter = malloc(sizeof(sliter));
		iter->dynamic = 1;
	}
	else {
		iter = &l->iter;
		iter->dynamic = 0;
	}

	iter->key = key;
	iter->l = (skiplist*)l;
	iter->p = q;
	iter->idx = imid;
	return iter;
}

int sl_nextkey(sliter *iter, void **val)
{
	if (!iter->p) {
		sl_done(iter);
		return 0;
	}

	if (iter->idx < iter->p->nbr) {
		if (iter->l->compkey(iter->p->bkt[iter->idx].key, iter->key) != 0) {
			sl_done(iter);
			return 0;
		}

		*val = iter->p->bkt[iter->idx++].val;
		return 1;
	}

	iter->p = iter->p->forward[0];
	iter->idx = 0;

	if (iter->p)
		return sl_nextkey(iter, val);

	sl_done(iter);
	return 0;
}

void sl_done(sliter *iter)
{
	iter->l->iter_cnt--;

	if (iter->dynamic)
		free(iter);
}

void sl_dump(const skiplist *l, const char *(*f)(void*, const void*), void *p1)
{
    slnode_t *p, *q;
    p = l->header;
    p = p->forward[0];

    while (p) {
        q = p->forward[0];
        printf("%6d: ", p->nbr);

        for (int j = 0; j < p->nbr; j++)
            printf("%s ", f(p1, p->bkt[j].key));

        printf("\n");
        p = q;
    }

    printf("\n");
}
