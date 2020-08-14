#pragma once

#include <string.h>

typedef struct skiplist_ skiplist;
typedef struct sliter_ sliter;

skiplist *sl_create(int (*compkey)(const void*, const void*));
int sl_set(skiplist *l, const void *k, const void *v);
int sl_app(skiplist *l, const void *k, const void *v);
int sl_get(const skiplist *l, const void *k, const void **v);
int sl_del(skiplist *l, const void *k);
void sl_iterate(const skiplist *l, int (*callback)(void *p, const void *k, const void *v), void *p);
void sl_find(const skiplist *l, const void *k, int (*f)(void *p, const void *k, const void *v), void *p);
sliter *sl_findkey(skiplist *l, const void *k);
int sl_nextkey(sliter *i, void **v);
void sl_done(sliter *i);
size_t sl_count(const skiplist *l);
void sl_dump(const skiplist *l, const char *(*f)(void *p, const void* k), void *p);
void sl_destroy(skiplist *l);
