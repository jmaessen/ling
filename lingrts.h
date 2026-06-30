#ifndef LING_RTS_H
#define LING_RTS_H

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>

#ifndef LING_INLINE
#define LING_INLINE inline
#endif

typedef union ling_obj {
  const void *whatever;
  const union ling_obj *ref;
  intptr_t int_val;
  uintptr_t uint_val;
  double double_val;
  char *string;
  union ling_obj (*func)();
} ling_obj;

typedef ling_obj ling_desc[4];

typedef struct ling_buf {
  // Ordered for hot fields first
  void *next_free; // >=start <= end
  void *end; // past last available word
  void *start;
} ling_buf;

typedef struct ling_region {
  void *next_free;
} ling_region;

typedef struct ling_config {
  size_t heap_size;
} ling_config;

typedef struct ling_context {
  // Ordered hot field first
  ling_buf heap;
  ling_config config;
} ling_context;

#define LING_REF(ptr) (ling_obj){ .ref = ptr }
#define LING_INT(i)   (ling_obj){ .int_val = i }
#define LING_UINT(u)  (ling_obj){ .uint_val = u }
#define LING_FLOAT(f) (ling_obj){ .double_val = f }
#define LING_STR(str) (ling_obj){ .string = str }
#define LING_DESC(d)  (ling_obj){ .ref = (const ling_obj *)d }
#define LING_FUNC(f)  (ling_obj){ .func = f }

#define LING_MK_DESC(desc, arity, func, name) \
  { LING_DESC(desc), LING_UINT(arity), LING_FUNC(func), LING_STR(name) }

// Fixed descriptors
extern const ling_desc ling_tuples[33]; // 0 through 32
extern const ling_desc ling_pAps[1][31];   // 1 through 31

extern const ling_desc _0p_CC; // Cons
extern const ling_desc Nil;

extern const ling_desc False;
extern const ling_desc True;

// General apply
ling_obj ling_apply(ling_context *ctxt, ling_obj clo, uintptr_t nargs, const ling_obj *args_in);

// Context and heap management
ling_context ling_init(ling_config);

LING_INLINE ling_region ling_begin_region(ling_context *ctxt) {
  return (ling_region){ .next_free = ctxt->heap.next_free };
}

LING_INLINE void ling_end_region(ling_context *ctxt, ling_region r) {
  assert(ctxt->heap.next_free >= r.next_free && ctxt->heap.start <= r.next_free);
  ctxt->heap.next_free = r.next_free;
}

noreturn void ling_oom(void);

// Allocate space for an object with n fields
LING_INLINE ling_obj *ling_buf_alloc_object(ling_buf *buf, size_t n) {
  ling_obj *res = buf->next_free;
  ling_obj *next_free = res + n + 1;
  buf->next_free = next_free;
  if (next_free > (ling_obj *)buf->end) ling_oom();
  return (ling_obj *)res;
}

#define LING_ALIGN(x) (((x) + sizeof(ling_obj) - 1) & ~(sizeof(ling_obj) - 1))

// Allocate space for a string with n bytes, leaving room for '\0'.
LING_INLINE char *ling_buf_alloc_string(ling_buf *buf, size_t n) {
  // Leave room for the trailing \0
  n = LING_ALIGN(n+1);
  char *res = buf->next_free;
  char *next_free = res + sizeof(ling_obj) + n;
  buf->next_free = next_free;
  if (next_free > (char *)buf->end) ling_oom();
  return res;
}
#undef LING_ALIGN

LING_INLINE ling_obj *ling_alloc_object(ling_context *ctxt, size_t n) {
  return ling_buf_alloc_object(&ctxt->heap, n);
}

LING_INLINE char *ling_alloc_string(ling_context *ctxt, size_t n) {
  return ling_buf_alloc_string(&ctxt->heap, n);
}

LING_INLINE int ling_desc_is(const ling_desc desc, ling_obj r) {
  return (r.ref[0].ref == &desc[0]);
}

LING_INLINE ling_obj ling_field(ling_obj r, uintptr_t i) {
  return (r.ref[i+1]);
}

LING_INLINE ling_obj *ling_mk_env(ling_context *ctxt, uintptr_t arity) {
  ling_obj *res = ling_alloc_object(ctxt, arity);
  res[0].ref = &ling_tuples[arity][0];
  return res;
}

LING_INLINE void ling_fill_env(uintptr_t arity, ling_obj *res, ling_obj *vals) {
  memcpy(res + 1, vals, arity * sizeof(ling_obj));
}

LING_INLINE ling_obj ling_new_obj(ling_context *ctxt, const ling_desc desc, ling_obj *args) {
  uintptr_t arity = desc[1].uint_val;
  ling_obj *res = ling_alloc_object(ctxt, arity);

  res[0].ref = &desc[0];
  ling_fill_env(arity, res, args);
  return LING_REF(res);
}

LING_INLINE ling_obj ling_pap(ling_context *ctxt, const ling_desc desc, uintptr_t arity, ling_obj *args) {
  ling_obj *res = ling_alloc_object(ctxt, arity + 1);

  res[0].ref = &ling_pAps[0][arity - 1][0];
  res[1].ref = &desc[0];
  memcpy(res + 2, args, arity * sizeof(ling_obj));
  return LING_REF(res);
}

LING_INLINE int ling_is_tuple(uintptr_t arity, ling_obj r) {
  return ling_desc_is(ling_tuples[arity], r);
}

LING_INLINE ling_obj ling_tuple(ling_context *ctxt, uintptr_t arity, ling_obj *args) {
  ling_obj *res = ling_alloc_object(ctxt, arity);

  res[0].ref = &ling_tuples[arity][0];
  ling_fill_env(arity, res, args);
  return LING_REF(res);
}

ling_buf ling_obj_buffer(ling_context *ctxt);

void ling_buffer_push(ling_buf *buf, ling_obj r);

void ling_buffer_append_char(ling_buf *buf, char c);

void ling_buffer_append_string(ling_buf *buf, char *str);

ling_obj *ling_buffer_finalize(ling_context *ctxt, ling_buf buf);

noreturn ling_obj ling_match_error(char *);

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
  LING_INLINE ling_obj name##_FUNC(ling_context *ctxt, ling_obj a)

#define P2(name) \
  extern const ling_desc name; \
  LING_INLINE ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b)

P2_DECL(strAppend);
P2_DECL(strAppendByte);

P1(strLength) {
  return LING_UINT(strlen(a.string));
}

P1_DECL(intToStr);

P2(byteAt) {
  return LING_UINT(a.string[b.uint_val]);
}

P2(strEq) {
  int r = strcmp(a.ref->string, b.ref->string);
  return LING_REF(r == 0 ? True : False);
}

P3_DECL(substr);
P1_DECL(strConcat);

P1(putStr) {
  fputs(a.string, stdout);
  return LING_REF(&ling_tuples[0][0]);
}

P1_DECL(lingDump);

#define PRIM_II_I(name, op) \
LING_INLINE ling_obj name##_FUNC(ling_context *_ctxt, ling_obj a, ling_obj b) { \
  return LING_INT(a.int_val op b.int_val);                                 \
} \
extern const ling_desc name

#define PRIM_II_B(name, op) \
LING_INLINE ling_obj name##_FUNC(ling_context *_ctxt, ling_obj a, ling_obj b) { \
  return LING_REF(a.int_val op b.int_val ? True : False);                  \
} \
extern const ling_desc name

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
#undef LING_INLINE

#endif
