#include "lingrts.h"
#include "lingrts_gen.c"

// Context and heap management
static void ling_heap_failure(size_t size) {
  fprintf(stderr, "Could not allocate heap of size %zu bytes\n", size);
  exit(EXIT_FAILURE);
}

static void ling_config_failure(void) {
  fprintf(stderr, "size_of(ling_ref) = %zu, not 8.\n", sizeof(ling_ref));
}

ling_context ling_init(ling_config config) {
  if (sizeof(ling_ref) != 8) ling_config_failure();
  const size_t mib = 1 << 20;
  if (config.size == 0) {
    config.size = 16 * mib;
  }
  size_t actual_size = (config.size + mib - 1) & ~(mib - 1);
  config.size = actual_size;
  void *start = aligned_alloc(2 * mib, actual_size);
  if (start == NULL) ling_heap_failure(actual_size);
  void *end = (char *)start + actual_size;
  return { config, { start, end, start } };
}

void ling_oom(void) {
  fprintf(stderr, "Out of memory\n");
  exit(EXIT_FAILURE);
}

ling_buf ling_obj_buffer(ling_context *ctxt, char *header) {
  ling_buf res = ctxt->heap;
  res.start = res.next_free;
  ling_obj *obj = ling_alloc_object(&res, 0);
  obj->header = header;
  return res;
}

void ling_buffer_push(ling_buf *buf, ling_ref r) {
  ling_ref *res = buf->next_free;
  buf->next_free = res + 1;
  if (buf->next_free > buf->end) ling_oom();
  *res = r;
}

void ling_buffer_append_char(ling_buf *buf, char c) {
  char *res = buf->next_free;
  buf->next_free = res + 1;
  if (buf->next_free >= buf->end) ling_oom();
  res[0] = c;
  res[1] = '\0';
}

void ling_buffer_append_string(ling_buf *buf, char *str) {
  char *res = buf->next_free;
  l = strlen(str);
  buf->next_free = res + l;
  // This must leave room for the trailing nul.
  if (buf->next_free >= buf->end) ling_oom();
  stpcpy(res, str);
}

static void ling_buf_misuse(void) {
  fprintf(stderr, "Heap advanced after buffer allocation and before finalize.\n");
  exit(EXIT_FAILURE);
}

#define LING_ALIGN(x) (((x) + sizeof(ling_ref) - 1) & ~(sizeof(ling_ref) - 1))

ling_obj *ling_buffer_finalize(ling_context *ctxt, ling_buf buf) {
  ling_obj *res = ctxt->heap.next_free;
  if (res != buf.start || ctxt->heap.end != buf.end) ling_buf_misuse();
  ctxt->heap.next_free = LING_ALIGN((char *)buf.next_free);
  return res;
}

///// Primitives

static void ling_bad_intToStr(void) {
  fprintf(stderr, "intToStr returned to many chars!\n");
  exit(EXIT_FAILURE);
}

#define P1(name) \
  const ling_desc name = { &name, 1, &name_func, #name }; \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a)

#define P2(name) \
  const ling_desc name = { &name, 2, &name_func, #name }; \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b)

#define P3(name)               \
  const ling_desc name = { &name, 3, &name_func, #name }; \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b, ling_obj c)

#define P1_DESC(name) \
  const ling_desc name = { &name, 1, &name_func, #name }

#define P2_DESC(name) \
  const ling_desc name = { &name, 2, &name_func, #name }

P2(strAppend) {
  ling_obj *res = ling_alloc_string(ctxt, strlen(a) + strlen(b));
  char *dest = res->string;
  dest = stpcpy(dest, a);
  stpcpy(dest, b);
  return {.ref = res};
}

P2(strAppendByte) {
  ling_obj *res = ling_alloc_string(ctxt, strlen(a) + 1);
  char *dest = res->string;
  dest = stpcpy(a, dest);
  dest[0] = (unsigned char)b.uint_val;
  dest[1] = '\0';
  return {.ref = res}
}

P1_DESC(strLength);


P1(intToStr) {
  char buf[32];
  int k = snprintf(&buf, sizeof(buf), "%w", a.int_val);
  if (k >= sizeof(buf)) ling_bad_intToStr();
  ling_obj *res = ling_alloc_string(ctxt, k);
  stpcpy(res->string, buf);
  return {.ref = res};
}

P2_DESC(byteAt);
P2_DESC(strEq);

// returns trailing string if len > strlen.  Still allocates len.
P3(substr) {
  ling_obj *res = &"";
  if (c.int_val > 0) {
    res = ling_alloc_string(ctxt, len);
    char *end = stpncpy(res->string, a.ref->string + b, c + 1);
    end[0] = '\0';
  }
  return {.ref = res};
}

/* Concatenate a list of strings */
P1(strConcat) {
  ling_buf buf = ling_obj_buffer(ctxt, STRING);
  for (; a.ref != Nil; a.ref = a.ref[2].ref) {
    ling_buffer_append_string(&buf, a.ref[1].string);
  }
  return {.ref = ling_buffer_finalize(ctxt, buf)};
}

P1_DESC(putStr);
