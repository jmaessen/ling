#ifndef LING_RTS_H
#define LING_RTS_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

union ling_obj {
  intptr_t int_val;
  uintptr_t uint_val;
  double double_val;
  struct ling_obj *ref;
  char *hdr;
  ling_val (*func)();
};

typedef union ling_obj ling_obj;

typedef ling_obj[4] ling_desc;

typedef struct ling_buf {
  void *start;
  void *end; // past last available word
  void *next_free; // >=start <= end
} ling_buf;

typedef struct ling_region {
  void *next_free;
} ling_region;

typedef struct ling_config {
  size_t heap_size;
} ling_config;

struct ling_context {
  ling_config config;
  ling_buf heap;
};

// Fixed descriptors
extern const ling_desc ling_tuples[33]; // 0 through 32
extern const ling_desc ling_pAps[30];   // 1 through 31

extern const ling_desc _0p_CC; // Cons
extern const ling_desc Nil;

extern const ling_desc False;
extern const ling_desc True;

// General apply
ling_obj ling_apply(ling_context *ctxt, ling_obj clo, int nargs, ling_obj *args_in);

// Context and heap management
ling_context ling_init(ling_config);

static ling_region ling_begin_region(ling_context *ctxt) {
  return ctxt->heap.next_free;
}

static void ling_end_region(ling_context *ctxt, ling_region r) {
  assert(ctxt->heap.next_free >= r.next_free && ctxt->heap.start <= r.next_free);
}

void ling_oom(void)

// Allocate space for an object with n fields
static ling_obj *ling_buf_alloc_object(ling_buf *buf, size_t n) {
  char *res = buf->next_free
  char *next_free = res + sizeof(ling_obj) + n * sizeof(ling_obj);
  buf->next_free = next_free;
  if (next_free > buf->end) ling_oom();
  return (ling_obj *)res;
}

static ling_obj *ling_alloc_object(ling_context *ctxt, size_t n) {
  return ling_buf_alloc_object(&ctxt->heap);
}

#define LING_ALIGN(x) (((x) + sizeof(ling_obj) - 1) & ~(sizeof(ling_obj) - 1))

// Allocate space for a string with n chars, leaving room for '\0'.
static ling_obj *ling_buf_alloc_string(ling_buf *buf, size_t n) {
  // Leave room for the trailing \0
  n = LING_ALIGN(n+1);
  char *res = buf->next_free;
  char *next_free = res + sizeof(ling_obj) + n;
  buf->next_free = next_free;
  if (next_free > buf->end) ling_oom();
  res->header = STRING;
  return res;
}
#undef LING_ALIGN

static ling_obj *ling_alloc_string(ling_context *ctxt, size_t n) {
  return ling_buf_alloc_string(&ctx->heap, n);
}

ling_buf ling_obj_buffer(ling_context *ctxt, char *header);

void ling_buffer_push(ling_buf *buf, ling_obj r);

void ling_buffer_append_char(ling_buf *buf, char c);

void ling_buffer_append_string(ling_buf *buf, char *str);

ling_obj *ling_buffer_finalize(ling_context *ctxt, ling_buf buf);

#define RETURN_VOID do { return { .ref = &VOID }; } while (0)

// Some primitives
#define P1_DECL(name) \
  extern const ling_desc name; \
  ling_obj name##_FUNC(ling_context *, ling_obj)

#define P2_DECL(name) \
  extern const ling_desc name; \
  ling_obj name##_FUNC(ling_context *, ling_obj, ling_obj)

#define P3_DECL(name) \
  extern const ling_desc name; \
  ling_obj name##_FUNC(ling_context *, ling_obj, ling_obj, ling_obj)

#define P1(name)                                          \
  extern const ling_desc name; \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a)

#define P2(name) \
  extern const ling_desc name; \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b)

P2_DECL(strAppend);
P2_DECL(strAppendByte);

P1(strLength) {
  return {.uint_val = strlen(a->string) };
}

P1_DECL(intToStr);

P2(byteAt) {
  return {.uint_val = a->string[b.uint_val]};
}

P2(strEq) {
  int r = strcmp(a.ref->string, b.ref->string);
  return r == 0 ? True : False;
}

P3_DECL(substr);
P1_DECL(strConcat);

P1(putStr) {
  fputs(a, stdout);
}

#define PRIM_II_I(name, op) \
static ling_obj name##_FUNC(ling_context *_ctxt, ling_obj a, ling_obj b) { \
  return {.int_val = a.int_val op b.int_val};                              \
}

#define PRIM_II_B(name, op)                                             \
static ling_obj name##_FUNC(ling_context *_ctxt, ling_obj a, ling_obj b) { \
  return  a.int_val op b.int_val ? True : False;                           \
}

PRIM_II_I(intAdd, +);
PRIM_II_I(intSub, -);
PRIM_II_I(intMul, *);
PRIM_II_I(intDiv, /);
PRIM_II_I(intMod, %);

PRIM_II_B(intEq, ==);
PRIM_II_B(intNE, !=);
PRIM_II_B(intLt, <);
PRIM_II_B(intLE, <=);
PRIM_II_B(intGt, >);
PRIM_II_B(intGE, >=);

#undef PRIM_II_I
#undef PRIM_II_B
#undef P1
#undef P2
#undef P1_DECL
#undef P2_DECL
#undef P3_DECL

#endif
