#pragma once

#include <stdint.h>

typedef struct {
    const char *name;
    const uint8_t *start;
    const uint8_t *end;
} library;

extern library g_libs[];

