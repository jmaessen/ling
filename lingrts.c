#include <inttypes.h>
// This line ensures the rts is the single home for
// these functions when not inlined (eg in the desc)
#define LING_INLINE extern inline
#include "lingrts.h"
#include "lingrts_gen.c"

// Context and heap management
noreturn static void ling_heap_failure(size_t size) {
  fprintf(stderr, "Could not allocate heap of size %zu bytes\n", size);
  exit(EXIT_FAILURE);
}

noreturn static void ling_config_failure(void) {
  fprintf(stderr, "size_of(ling_ref) = %zu, not 8.\n", sizeof(ling_obj *));
  exit(EXIT_FAILURE);
}

ling_context ling_init(ling_config config) {
  if (sizeof(ling_obj *) != 8) ling_config_failure();
  const size_t mib = 1 << 20;
  if (config.heap_size == 0) {
    config.heap_size = 16 * mib;
  }
  size_t actual_size = (config.heap_size + mib - 1) & ~(mib - 1);
  config.heap_size = actual_size;
  void *start = aligned_alloc(2 * mib, actual_size);
  if (start == NULL) ling_heap_failure(actual_size);
  void *end = (char *)start + actual_size;
  return (ling_context){ { start, end, start }, config };
}

noreturn void ling_oom(void) {
  fprintf(stderr, "Out of memory\n");
  exit(EXIT_FAILURE);
}

ling_buf ling_obj_buffer(ling_context *ctxt) {
  ling_buf res = ctxt->heap;
  res.start = res.next_free;
  return res;
}

void ling_buffer_push(ling_buf *buf, ling_obj r) {
  ling_obj *res = buf->next_free;
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
  buf->next_free = res + strlen(str);
  // This must leave room for the trailing nul.
  if (buf->next_free >= buf->end) ling_oom();
  stpcpy(res, str);
}

noreturn static void ling_buf_misuse(void) {
  fprintf(stderr, "Heap advanced after buffer allocation and before finalize.\n");
  exit(EXIT_FAILURE);
}

#define LING_ALIGN(x) (void *)(((uintptr_t)(x) + sizeof(ling_obj) - 1) & ~(sizeof(ling_obj) - 1))

ling_obj *ling_buffer_finalize(ling_context *ctxt, ling_buf buf) {
  ling_obj *res = ctxt->heap.next_free;
  if (res != buf.start || ctxt->heap.end != buf.end) ling_buf_misuse();
  ctxt->heap.next_free = LING_ALIGN((char *)buf.next_free);
  return res;
}

noreturn ling_obj ling_match_error(char *message) {
  fprintf(stderr, "%sMatch error.\n", message);
  exit(EXIT_FAILURE);
}

///// Primitives

noreturn static void ling_bad_intToStr(void) {
  fprintf(stderr, "intToStr returned to many chars!\n");
  exit(EXIT_FAILURE);
}

#define P1(name) \
  const ling_desc name = LING_MK_DESC( &name, 1, name##_FUNC, #name ); \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a)

#define P2(name) \
  const ling_desc name = LING_MK_DESC( &name, 2, name##_FUNC, #name ); \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b)

#define P3(name)               \
  const ling_desc name = LING_MK_DESC( &name, 3, name##_FUNC, #name ); \
  ling_obj name##_FUNC(ling_context *ctxt, ling_obj a, ling_obj b, ling_obj c)

#define P1_DESC(name) \
  const ling_desc name = LING_MK_DESC( &name, 1, name##_FUNC, #name )

#define P2_DESC(name) \
  const ling_desc name = LING_MK_DESC( &name, 2, name##_FUNC, #name )

P2(strAppend) {
  char *res = ling_alloc_string(ctxt, strlen(a.string) + strlen(b.string));
  char *dest = res;
  dest = stpcpy(dest, a.string);
  stpcpy(dest, b.string);
  return LING_STR(res);
}

P2(strAppendByte) {
  char *res = ling_alloc_string(ctxt, strlen(a.string) + 1);
  char *dest = res;
  dest = stpcpy(a.string, dest);
  dest[0] = (unsigned char)b.uint_val;
  dest[1] = '\0';
  return LING_STR(res);
}

P1_DESC(strLength);


P1(intToStr) {
  char buf[32];
  int k = snprintf(&buf[0], sizeof(buf), "%" PRIdPTR, a.int_val);
  if (k >= sizeof(buf)) ling_bad_intToStr();
  char *res = ling_alloc_string(ctxt, k);
  stpcpy(res, buf);
  return LING_STR(res);
}

P2_DESC(byteAt);
P2_DESC(strEq);

// returns trailing string if len > strlen.  Still allocates len.
P3(substr) {
  char *res = "";
  if (c.int_val > 0) {
    res = ling_alloc_string(ctxt, c.uint_val + 1);
    char *end = stpncpy(res, a.string + b.uint_val, c.uint_val);
    end[1] = '\0';
  }
  return LING_STR(res);
}

/* Concatenate a list of strings */
P1(strConcat) {
  ling_buf buf = ling_obj_buffer(ctxt);
  for (; a.ref != Nil; a.ref = a.ref[2].ref) {
    ling_buffer_append_string(&buf, a.ref[1].string);
  }
  return LING_STR((char *)ling_buffer_finalize(ctxt, buf));
}

P1_DESC(putStr);
P2_DESC(intAdd);
P2_DESC(intSub);
P2_DESC(intMul);
P2_DESC(intDiv);
P2_DESC(intMod);

P2_DESC(intEq);
P2_DESC(intNE);
P2_DESC(intLt);
P2_DESC(intLE);
P2_DESC(intGt);
P2_DESC(intGE);

// Heap dumping nonsense

// Static (initialized) data can be scattered across several sections, so we
// record a list of [start, start+size) ranges rather than a single span.
#define LING_MAX_INITDATA_RANGES 8
struct dumpmetadata {
  int n;
  struct { uintptr_t start, size; } ranges[LING_MAX_INITDATA_RANGES];
};

#if defined(__APPLE__)
  #include <mach-o/dyld.h>
  #include <mach-o/getsect.h>
  /* macOS Mach-O mapping via getsect.h functions */
  void dump_metadata_init(struct dumpmetadata *md) {
    const struct mach_header_64 *header =
      (const struct mach_header_64 *)_dyld_get_image_header(0);
    static const char *const specs[][2] = {
      {"__DATA_CONST", "__const"},   // descriptors (relocated const)
      {"__TEXT",       "__cstring"}, // name strings / string literals
      {"__TEXT",       "__const"},   // pure read-only consts (precompiled structs)
      {"__DATA",       "__const"},   // const data that ended up in writable segment
      {"__DATA",       "__data"},    // mutable initialized data, if any
    };
    md->n = 0;
    for (int i = 0; i < (int)(sizeof(specs) / sizeof(specs[0])); ++i) {
      unsigned long size = 0;
      uint8_t *p = getsectiondata(header, specs[i][0], specs[i][1], &size);
      if (p && size && md->n < LING_MAX_INITDATA_RANGES) {
        md->ranges[md->n].start = (uintptr_t)p;
        md->ranges[md->n].size = (uintptr_t)size;
        md->n++;
      }
    }
  }
#elif defined(__linux__)
  // On ELF [etext, edata) spans .rodata + .data, covering both descriptors and
  // string constants.
  void dump_metadata_init(struct dumpmetadata *md) {
    extern char etext[], edata[];
    md->n = 1;
    md->ranges[0].start = (uintptr_t)etext;
    md->ranges[0].size = (uintptr_t)edata - (uintptr_t)etext;
  }
#else
  void dump_metadata_init(struct dumpmetadata *md) { md->n = 0; }
#endif

static int inInitData(struct dumpmetadata *md, ling_obj o) {
  uintptr_t p = o.uint_val;
  for (int i = 0; i < md->n; ++i) {
    uintptr_t start = md->ranges[i].start;
    if (start <= p && p < start + md->ranges[i].size) return 1;
  }
  return 0;
}

inline static int aligned(ling_obj o) {
  return (o.uint_val & 0x7) == 0;
}

inline static int inHeap(ling_context *ctxt, ling_obj o) {
  return ctxt->heap.start <= (void *)o.ref &&
    (void *)o.ref < ctxt->heap.next_free &&
    aligned(o);
}

inline static int looksLikeHeader(struct dumpmetadata *md, ling_obj o) {
  return inInitData(md, o) && aligned(o) &&
    0 <= o.ref[1].int_val && o.ref[1].int_val < 32 &&
    inInitData(md, o.ref[3]) && strnlen(o.ref[3].string, 50) < 50;
}

static void dump_rec(ling_context *ctxt, struct dumpmetadata *md,
                     ling_obj o, int lvl, int comma_sep) {
  const char* sep = comma_sep ? ",\n" : "\n";
  do {
    if (inHeap(ctxt, o)) {
      const ling_obj *p = o.ref;
      const ling_obj desc = p[0];
      const ling_obj *dr = desc.ref;
      if (!looksLikeHeader(md, desc) || dr[1].int_val <= 0) {
        printf("%*s\"%.50s\"%s", lvl * 2, "", o.string, sep);
        break;
      }
      printf("%*s%.50s%s", lvl * 2, "", dr[3].string, sep);
      const uintptr_t arity = dr[1].uint_val;
      for (int i = 1; i < arity; ++i) {
        dump_rec(ctxt, md, p[i], lvl + 1, 0);
      }
      o = p[arity];
      continue;
    } else if (inInitData(md, o)) {
      if (looksLikeHeader(md, o)) {
        printf("%*s%.50s%s", lvl * 2, "", o.ref[3].string, sep);
      } else {
        // Assume other static data is string data, which
        // is actually subtly wrong as we can pre-compile
        // constant structures.
        printf("%*s\"%.50s\"%s", lvl * 2, "", o.string, sep);
      }
      break;
    } else {
      // Treat it as a number (we might want to add float printing here too?)
      printf("%*s%ld (%lx)%s", lvl * 2, "", o.int_val, o.uint_val, sep);
      break;
    }
  } while (1);
}

P1(lingDump) {
  struct dumpmetadata md;
  dump_metadata_init(&md);
  dump_rec(ctxt, &md, a, 0, 0);
  return LING_REF(&ling_tuples[0][0]);
}

int main(int argc, char *argv[]) {
  extern ling_obj initialize(ling_context *);
  setlinebuf(stdin);
  ling_config conf = {64*1024*1024};
  ling_context ctxt = ling_init(conf);
  ling_obj res = initialize(&ctxt);
  lingDump_FUNC(&ctxt, res);
}
