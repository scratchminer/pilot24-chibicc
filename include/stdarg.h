#ifndef __STDARG_H
#define __STDARG_H

typedef struct {
  unsigned int gp_offset;
  unsigned int fp_offset;
  unsigned int dp_offset;
  void *overflow_arg_area;
  void *reg_save_area;
} __va_elem;

typedef __va_elem va_list[1];

#define va_start(ap, last) \
  do { *(ap) = *(__va_elem *)__va_area__; } while (0)

#define va_end(ap)

static void *__va_arg_mem(__va_elem *ap, int sz, int align) {
  void *p = ap->overflow_arg_area;
  ap->overflow_arg_area = ((unsigned int)p + sz + 1) / 2 * 2;
  return p;
}

static void *__va_arg_gp(__va_elem *ap, int sz, int align) {
  if (ap->gp_offset >= 44)
    return __va_arg_mem(ap, sz, align);

  void *r = ap->reg_save_area + ap->gp_offset;
  ap->gp_offset += align;
  return r;
}

static void *__va_arg_fp(__va_elem *ap, int sz, int align) {
  if (ap->fp_offset >= 52)
    return __va_arg_mem(ap, sz, align);

  void *r = ap->reg_save_area + ap->fp_offset;
  ap->fp_offset += 4;
  return r;
}

static void *__va_arg_dp(__va_elem *ap, int sz, int align) {
  if (ap->dp_offset >= 76)
    return __va_arg_mem(ap, sz, align);

  void *r = ap->reg_save_area + ap->dp_offset;
  ap->dp_offset += 8;
  return r;
}

#define va_arg(ap, ty)                                                  \
  ({                                                                    \
    int klass = __builtin_reg_class(ty);                                \
    *(ty *)(klass == 0 ? __va_arg_gp(ap, sizeof(ty), _Alignof(ty)) :    \
            klass == 1 ? __va_arg_fp(ap, sizeof(ty), _Alignof(ty)) :    \
            klass == 2 ? __va_arg_dp(ap, sizeof(ty), _Alignof(ty)) :    \
            __va_arg_mem(ap, sizeof(ty), _Alignof(ty)));                \
  })

#define va_copy(dest, src) ((dest)[0] = (src)[0])

#define __GNUC_VA_LIST 1
typedef va_list __gnuc_va_list;

#endif
