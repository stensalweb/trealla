#pragma once

#include <stdio.h>

/*
 *  These relate to similar stdc functions...
 */

extern int readc_utf8(int fd, int *ch);
extern int getc_utf8(FILE *fp);
extern size_t strlen_utf8(const char *s);
extern int isalpha_utf8(int ch);
extern int isalnum_utf8(int ch);
extern const char *strchr_utf8(const char *s, int ch);
extern const char *strrchr_utf8(const char *s, int ch);

extern size_t substrlen_utf8(const char *s, const char *end);

/*
 *  These just get/put a memory buffer...
 */

extern int get_char_utf8(const char **src);
extern int peek_char_utf8(const char *src);
extern int put_char_utf8(char *dst, int ch);
extern int put_char_bare_utf8(char *dst, int ch);
extern int put_len_utf8(int ch);
extern int is_char_utf8(const char *src);
extern int len_char_utf8(const char *src);
