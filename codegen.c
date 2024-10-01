#include "chibicc.h"

#define GP_MAX 2
#define FP_MAX 2
#define DP_MAX 2
#define LP_MAX 2

#define GP_SCRATCH_START 2
#define GP_SCRATCH_END 6

static FILE *output_file;
static int depth;
static Obj *current_fn;

static int indents;

static int to_gp_reg, to_fp_reg, to_dp_reg, to_lp_reg;

static bool gen_expr(Node *node, bool collapse, bool override);
static void gen_stmt(Node *node);

__attribute__((format(printf, 1, 2)))
static void println(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(output_file, fmt, ap);
  va_end(ap);
  fprintf(output_file, "\n");
}

__attribute__((format(printf, 1, 2)))
static void debug(char *fmt, ...) {
  /*for (int i = 0; i < indents; i++)
    printf(" ");
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf("\n");*/
}

static int count(void) {
  static int i = 1;
  return i++;
}

static char get_suffix(int sz) {
  switch (sz) {
    case 1: return 'b';
    case 2: return 'w';
    case 3: return 'p';
  }
  unreachable();
}

static char get_stack_reg(int sz) {
  switch (sz) {
    case 1: return 'l';
    case 2: return 'w';
    case 3: return 'p';
  }
  unreachable();
}

static void push(int sz, int from_reg) {
  if (sz == 1) sz = 2;
  if (sz < 4) {
    println("\tld.%c @-sp, %c%d", get_suffix(sz), get_stack_reg(sz), from_reg);
    if (sz == 3) depth += 4;
    else depth += sz;
  }
  else {
    println("\tld.w @-sp, @__long_%d1", from_reg);
    println("\tld.w @-sp, @__long_%d0", from_reg);
    depth += 4;
  }
}

static void pop(int sz, int to_reg) {
  if (sz == 1) sz = 2;
  if (sz < 4) {
    println("\tld.%c %c%d, @sp+", get_suffix(sz), get_stack_reg(sz), to_reg);
    if (sz == 3) depth -= 4;
    else depth -= sz;
  }
  else {
    println("\tld.w @__long_%d0, @sp+", to_reg);
    println("\tld.w @__long_%d1, @sp+", to_reg);
    depth -= 4;
  }
}

static void pushf(int sz, int from_reg) {
  if (sz == 8) {
    println("\tld.w @-sp, @__double_%d3", from_reg);
    println("\tld.w @-sp, @__double_%d2", from_reg);
    println("\tld.w @-sp, @__double_%d1", from_reg);
    println("\tld.w @-sp, @__double_%d0", from_reg);
  }
  else {
    println("\tld.w @-sp, @__float_%d1", from_reg);
    println("\tld.w @-sp, @__float_%d0", from_reg);
  }
  depth += sz;
}

static void popf(int sz, int to_reg) {
  if (sz == 8) {
    println("\tld.w @__double_%d0, @sp+", to_reg);
    println("\tld.w @__double_%d1, @sp+", to_reg);
    println("\tld.w @__double_%d2, @sp+", to_reg);
    println("\tld.w @__double_%d3, @sp+", to_reg);
  }
  else {
    println("\tld.w @__float_%d0, @sp+", to_reg);
    println("\tld.w @__float_%d1, @sp+", to_reg);
  }
  depth -= sz;
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
int align_to(int n, int align) {
  return (n + align - 1) / align * align;
}

// Compute the absolute address of a given node.
// It's an error if a given node does not reside in memory.
static void gen_addr(Node *node, int to_reg) {
  switch (node->kind) {
    case ND_VAR:
      // Variable-length array, which is always local.
      if (node->var->ty->kind == TY_VLA) {
        println("\tld.p p%d, @p6+%d", to_reg, node->var->offset);
        return;
      }

      // Local variable
      if (node->var->is_local) {
        println("\tlea p%d, @p6+%d", to_reg, node->var->offset);
        return;
      }

      // Here, we generate an absolute address of a function or a global
      // variable. Even though they exist at a certain address at runtime,
      // their addresses are not known at link-time for the following
      // two reasons.
      //
      //  - Address randomization: Executables are loaded to memory as a
      //    whole but it is not known what address they are loaded to.
      //    Therefore, at link-time, relative address in the same
      //    exectuable (i.e. the distance between two functions in the
      //    same executable) is known, but the absolute address is not
      //    known.
      //
      //  - Dynamic linking: Dynamic shared objects (DSOs) or .so files
      //    are loaded to memory alongside an executable at runtime and
      //    linked by the runtime loader in memory. We know nothing
      //    about addresses of global stuff that may be defined by DSOs
      //    until the runtime relocation is complete.
      //
      // In order to deal with the former case, we use RIP-relative
      // addressing, denoted by `(%rip)`. For the latter, we obtain an
      // address of a stuff that may be in a shared object file from the
      // Global Offset Table using `@GOTPCREL(%rip)` notation.

      // Function
      if (node->ty->kind == TY_FUNC) {
        println("\tld.p p%d, %s", to_reg, node->var->name);
        return;
      }
      
      // Global variable
      println("\tlea p%d, @%s", to_reg, node->var->name);
      return;
    case ND_DEREF:
      gen_expr(node->lhs, true, false);
      return;
    case ND_COMMA:
      gen_expr(node->lhs, true, false);
      gen_addr(node->rhs, true);
      return;
    case ND_MEMBER: {
      if (node->lhs->kind == ND_VAR) {
        if (node->lhs->var->is_local) {
          println("\tld.p p%d, @p6+%d", to_reg, node->lhs->var->offset + node->member->offset);
          return;
        }
        println("\tlea p%d, @%s+%d", to_reg, node->lhs->var->name, node->member->offset);
        return;
      }
      else {
        gen_addr(node->lhs, to_reg);
        if ((node->member->offset > 0) && (node->member->offset <= 8))
          println("\tadq.p p%d, %d", to_reg, node->member->offset);
        else if (node->member->offset > 0)
          println("\tadd.p p%d, %d", to_reg, node->member->offset);
      }
    }
    case ND_FUNCALL:
      if (node->ret_buffer) {
        gen_expr(node, true, false);
        return;
      }
      break;
    case ND_ASSIGN:
    case ND_COND:
      if (node->ty->kind == TY_STRUCT || node->ty->kind == TY_UNION) {
        gen_expr(node, true, false);
        return;
      }
      break;
    case ND_VLA_PTR:
      println("\tlea p%d, @p6+%d", to_reg, node->var->offset);
      return;
    default:
      error_tok(node->tok, "not an lvalufe");
      return;
  }
}

// Load a value to to_reg from where from_ptr is pointing to.
static void load(Type *ty, int to_reg, int from_ptr) {
  switch (ty->kind) {
    case TY_ARRAY:
    case TY_STRUCT:
    case TY_UNION:
    case TY_FUNC:
    case TY_VLA:
      // If it is an array, do not attempt to load a value to the
      // register because in general we can't load an entire array to a
      // register. As a result, the result of an evaluation of an array
      // becomes not the array itself but the address of the array.
      // This is where "array is automatically converted to a pointer to
      // the first element of the array in C" occurs.
      return;
    case TY_LONG:
    case TY_ENUM:
      println("\tld.w @__long_%d0, @p%d+", to_reg, from_ptr);
      println("\tld.w @__long_%d1, @p%d+", to_reg, from_ptr);
      return;
    case TY_FLOAT:
      println("\tld.w @__float_%d0, @p%d+", to_reg, from_ptr);
      println("\tld.w @__float_%d1, @p%d+", to_reg, from_ptr);
      return;
    case TY_DOUBLE:
      println("\tld.w @__double_%d0, @p%d+", to_reg, from_ptr);
      println("\tld.w @__double_%d1, @p%d+", to_reg, from_ptr);
      println("\tld.w @__double_%d2, @p%d+", to_reg, from_ptr);
      println("\tld.w @__double_%d3, @p%d+", to_reg, from_ptr);
      return;
    default:
      break;
  }

  char *insn = ty->is_unsigned ? "ldzx" : "ldsx";

  // When we load a char or a short value to a register, we always
  // extend them to the size of int, so we can assume the lower half of
  // a register always contains a valid value. The upper half of a
  // register for char, short and int may contain garbage. When we load
  // a long value to a register, it simply occupies the entire register.
  if (ty->size < 3)
    println("\t%s.%c p%d, @p%d", insn, get_suffix(ty->size), to_reg, from_ptr);
  else if (ty->size == 3)
    println("\tld.p p%d, @p%d", to_reg, from_ptr);
}

// Store from_reg to the address that to_ptr is pointing to.
// If to_ptr < 0, it will use the stack top instead.
static void store(Type *ty, int to_ptr, int from_reg) {
  if (to_ptr >= 0) {
    switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        for (int i = 0; i < ty->size - 2; i += 2)
          println("\tld.w @p%d+, @p%d+", to_ptr, from_reg);
        println("\tld.w @p%d, @p%d+", to_ptr, from_reg);
        return;
      case TY_FLOAT:
        println("\tld.w @p%d+, @__float_%d0", to_ptr, from_reg);
        println("\tld.w @p%d, @__float_%d1", to_ptr, from_reg);
        return;
      case TY_DOUBLE:
        println("\tld.w @p%d+, @__double_%d0", to_ptr, from_reg);
        println("\tld.w @p%d+, @__double_%d1", to_ptr, from_reg);
        println("\tld.w @p%d+, @__double_%d2", to_ptr, from_reg);
        println("\tld.w @p%d, @__double_%d3", to_ptr, from_reg);
        return;
      default:
        break;
    }
  
    if (ty->size <= 3) {
      char suffix = get_suffix(ty->size);
      char reg = get_stack_reg(ty->size);
      println("\tld.%c @p%d, %c%d", suffix, to_ptr, reg, from_reg);
    }
    else {
      println("\tld.w @p%d+, @__long_%d0", to_ptr, from_reg);
      println("\tld.w @p%d, @__long_%d1", to_ptr, from_reg);
    }
  }
  else {
    println("\tld.p @-sp, p0");
    println("\tld.p p0, @sp+4");
    
    depth -= 4;
    
    switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        if (from_reg != 0) {
          for (int i = 0; i < ty->size; i += 2)
             println("\tld.w @p0+, @p%d+", from_reg);
        }
        println("\tld.p p0, @sp+");
        println("\tadq.p sp, 4");
        return;
      case TY_FLOAT:
        println("\tld.w @p0+, @__float_%d0", from_reg);
        println("\tld.w @p0+, @__float_%d1", from_reg);
        println("\tld.p p0, @sp+");
        println("\tadq.p sp, 4");
        return;
      case TY_DOUBLE:
        println("\tld.w @p0+, @__double_%d0", from_reg);
        println("\tld.w @p0+, @__double_%d1", from_reg);
        println("\tld.w @p0+, @__double_%d2", from_reg);
        println("\tld.w @p0+, @__double_%d3", from_reg);
        println("\tld.p p0, @sp+");
        println("\tadq.p sp, 4");
        return;
      default:
        break;
    }
  
    if (ty->size <= 3) {
      char suffix = get_suffix(ty->size);
      char reg = get_stack_reg(ty->size);
      println("\tld.%c @p0, %c%d", suffix, reg, from_reg);
    }
    else {
      println("\tld.w @p0+, @__long_%d0", from_reg);
      println("\tld.w @p0+, @__long_%d1", from_reg);
    }
    println("\tld.p p0, @sp+");
    println("\tadq.p sp, 4");
  }
}

static void cmp_zero(Type *ty, int from_reg) {
  switch (ty->kind) {
    case TY_FLOAT: {
      int c = count();
      println("\tcp.w @__float_%d0, $0000", from_reg);
      println("\tjr ne, __L_nonzero_%d", c);
      println("\tld.w w0, @__float_%d1", from_reg);
      println("\tand.w w0, $7fff");
      println("\tcp.w w0, $0000");
      println("__L_nonzero_%d:", c);
      return;
    }
    case TY_DOUBLE: {
      int c = count();
      println("\tcp.w @__double_%d0, $0000", from_reg);
      println("\tjr ne, __L_nonzero_%d", c);
      println("\tcp.w @__double_%d1, $0000", from_reg);
      println("\tjr ne, __L_nonzero_%d", c);
      println("\tcp.w @__double_%d2, $0000", from_reg);
      println("\tjr ne, __L_nonzero_%d", c);
      println("\tld.w w0, @__double_%d3", from_reg);
      println("\tand.w w0, $7fff");
      println("\tcp.w w0, $0000");
      println("__L_nonzero_%d:", c);
      return;
    }
    default:
      break;
  }

  if (is_integer(ty) && ty->size <= 3) {
    if (ty->size == 1) {
      println("\tcp.p p%d, 0", from_reg);
    }
    else {
      println("\tcp.%c %c%d, 0", get_suffix(ty->size), get_stack_reg(ty->size), from_reg);
    }
  }
  else {
    int c = count();
    println("\tcp.w @__long_%d0, $0000", from_reg);
    println("\tjr ne, __L_nonzero_%d", c);
    println("\tcp.w @__long_%d1, $0000", from_reg);
    println("__L_nonzero_%d:", c);
  }
}

enum { I8, I16, I24, I32, U8, U16, U24, U32, F32, F64 };

static int getTypeId(Type *ty) {
  switch (ty->kind) {
    case TY_CHAR:
      return ty->is_unsigned ? U8 : I8;
    case TY_SHORT:
      return ty->is_unsigned ? U16 : I16;
    case TY_INT:
      return ty->is_unsigned ? U24 : I24;
    case TY_LONG:
    case TY_ENUM:
      return ty->is_unsigned ? U32 : I32;
    case TY_FLOAT:
      return F32;
    case TY_DOUBLE:
      return F64;
    default:
      return U24;
  }
}

// The table for type casts
static char i24i8[] = "ldsx.b p0, l0";
static char i24u8[] = "ldzx.b p0, l0";
static char i24i16[] = "ldsx.w p0, w0";
static char i24u16[] = "ldzx.w p0, w0";
static char i24i32[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldsx.b p0, l0\n\tld.w @__long_21, w0";
static char i24u32[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldzx.b p0, l0\n\tld.w @__long_21, w0";
static char i24f32[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldsx.b p0, l0\n\tld.w @__long_21, w0\n\tcall __floatsisf";
static char i24f64[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldsx.b p0, l0\n\tld.w @__long_21, w0\n\tcall __floatsidf";

static char u24f32[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldzx.b p0, l0\n\tld.w @__long_21, w0\n\tcall __floatunsisf";
static char u24f64[] = "ld.p @__long_20, p0\n\tld.w w0, @__long_21\n\tldzx.b p0, l0\n\tld.w @__long_21, w0\n\tcall __floatunsidf";

static char i32i8[] = "ldsx.b p0, @__long_20";
static char i32u8[] = "ldzx.b p0, @__long_20";
static char i32i16[] = "ldsx.w p0, @__long_20";
static char i32u16[] = "ldzx.w p0, @__long_20";
static char i32u24[] = "ld.p p0, @__long_20";
static char i32f32[] = "call __floatdisf";
static char i32f64[] = "call __floatdidf";

static char u32f32[] = "call __floatundisf";
static char u32f64[] = "call __floatundidf";

static char f32i8[] = "call __fixsfsi\n\tldsx.b p0, @__long_20";
static char f32u8[] = "call __fixunssfsi\n\tldzx.b p0, @__long_20";
static char f32i16[] = "call __fixsfsi\n\tldsx.w p0, @__long_20";
static char f32u16[] = "call __fixunssfsi\n\tldzx.w p0, @__long_20";
static char f32i24[] = "call __fixsfsi\n\tld.p p0, @__long_20";
static char f32u24[] = "call __fixunssfsi\n\tld.p p0, @__long_20";
static char f32i32[] = "call __fixsfsi";
static char f32u32[] = "call __fixunssfsi";
static char f32f64[] = "call __extendsfdf2";

static char f64i8[] = "call __fixdfsi\n\tldsx.b p0, @__long_20";
static char f64u8[] = "call __fixunsdfsi\n\tldzx.b p0, @__long_20";
static char f64i16[] = "call __fixdfsi\n\tldsx.w p0, @__long_20";
static char f64u16[] = "call __fixunsdfsi\n\tldzx.w p0, @__long_20";
static char f64i24[] = "call __fixdfsi\n\tld.p p0, @__long_20";
static char f64u24[] = "call __fixunsdfsi\n\tld.p p0, @__long_20";
static char f64i32[] = "call __fixdfsi";
static char f64u32[] = "call __fixunsdfsi";
static char f64f32[] = "call __truncdfsf2";

static char *cast_table[][10] = {
  // i8   i16     i24     i32     u8     u16     u24     u32     f32     f64
  {NULL,  i24i16, i24i8,  i24i32, i24u8, i24u16, NULL,   i24u32, i24f32, i24f64}, // i8
  {i24i8, NULL,   i24i16, i24i32, i24u8, i24u16, NULL,   i24u32, i24f32, i24f64}, // i16
  {i24i8, i24i16, NULL,   i24i32, i24u8, i24u16, NULL,   i24u32, i24f32, i24f64}, // i24
  {i32i8, i32i16, i32u24, NULL,   i32u8, i32u16, i32u24, NULL,   i32f32, i32f64}, // i32

  {i24i8, i24i16, i24u8,  i24i32, NULL,  NULL,   NULL,   i24u32, u24f32, u24f64}, // u8
  {i24i8, i24i16, i24u16, i24i32, i24u8, NULL,   NULL,   i24u32, u24f32, u24f64}, // u16
  {i24i8, i24i16, NULL,   i24i32, i24u8, i24u16, NULL,   i24u32, u24f32, u24f64}, // u24
  {i32i8, i32i16, i32u24, NULL,   i32u8, i32u16, i32u24, NULL,   u32f32, u32f64}, // u32

  {f32i8, f32i16, f32i24, f32i32, f32u8, f32u16, f32u24, f32u32, NULL,   f32f64}, // f32
  {f64i8, f64i16, f64i24, f64i32, f64u8, f64u16, f64u24, f64u32, f64f32, NULL  }, // f64
};

static void cast(Type *from, Type *to, int from_reg, int to_reg) {
  if (to->kind == TY_VOID)
    return;

  if (to->kind == TY_BOOL) {
    int c = count();
    cmp_zero(from, from_reg);
    println("\tjr z, __L_zero_%d", c);
    println("\tldq p%d, $01", to_reg);
    println("\tjr.s __L_nonzero_%d", c);
    println("__L_zero_%d:", c);
    println("\tldq p%d, $00", to_reg);
    println("__L_nonzero_%d:", c);
    return;
  }
  
  int t1 = getTypeId(from);
  int t2 = getTypeId(to);
  
  if (cast_table[t1][t2]) {
    if (from->kind == TY_FLOAT) {
      println("\tld.w @__softfp_tmp00, @__float_%d0", from_reg);
      println("\tld.w @__softfp_tmp01, @__float_%d1", from_reg);
    }
    else if (from->kind == TY_DOUBLE) {
      println("\tld.w @__softfp_tmp00, @__double_%d0", from_reg);
      println("\tld.w @__softfp_tmp01, @__double_%d1", from_reg);
      println("\tld.w @__softfp_tmp02, @__double_%d2", from_reg);
      println("\tld.w @__softfp_tmp03, @__double_%d3", from_reg);
    }
    else if (from->kind == TY_LONG || from->kind == TY_ENUM) {
      println("\tld.w @__long_20, @__long_%d0", from_reg);
      println("\tld.w @__long_21, @__long_%d1", from_reg);
    }
    else if (from_reg != 0) {
      char suffix = get_suffix(from->size);
      char reg = get_stack_reg(from->size);
      println("\tld.%c %c0, %c%d", suffix, reg, reg, from_reg);
    }
    println("\t%s", cast_table[t1][t2]);
    if (to->kind == TY_FLOAT) {
      println("\tld.w @__float_%d0, @__softfp_tmp00", to_reg);
      println("\tld.w @__float_%d1, @__softfp_tmp01", to_reg);
    }
    else if (to->kind == TY_DOUBLE) {
      println("\tld.w @__double_%d0, @__softfp_tmp00", to_reg);
      println("\tld.w @__double_%d1, @__softfp_tmp01", to_reg);
      println("\tld.w @__double_%d2, @__softfp_tmp02", to_reg);
      println("\tld.w @__double_%d3, @__softfp_tmp03", to_reg);
    }
    else if (to->kind == TY_LONG || from->kind == TY_ENUM) {
      println("\tld.w @__long_%d0, @__long_20", to_reg);
      println("\tld.w @__long_%d1, @__long_21", to_reg);
    }
    else if (to_reg != 0) {
      char suffix = get_suffix(to->size);
      char reg = get_stack_reg(to->size);
      if (to->size == 1) {
        suffix = get_suffix(3);
        reg = get_stack_reg(3);
      }
      println("\tld.%c %c%d, %c0", suffix, reg, to_reg, reg);
    }
  }
}

static void push_struct(Type *ty, int from_reg) {
  int sz = align_to(ty->size, 2);
  depth += sz;
  
  for (int i = 0; i < sz; i += 2)
    println("\tld.w @-sp, @p%d+%d", from_reg, i);
}

static void push_args2(Node *args, bool first_pass) {
  if (!args)
    return;
  push_args2(args->next, first_pass);
  
  if ((first_pass && !args->pass_by_stack) || (!first_pass && args->pass_by_stack))
    return;
  gen_expr(args, true, false);
  
  switch (args->ty->kind) {
    case TY_STRUCT:
    case TY_UNION:
      push_struct(args->ty, to_gp_reg);
      break;
    case TY_FLOAT:
      pushf(args->ty->size, to_fp_reg);
      break;
    case TY_DOUBLE:
      pushf(args->ty->size, to_dp_reg);
      break;
    case TY_ARRAY:
      push(3, to_gp_reg);
      break;
    case TY_LONG:
    case TY_ENUM:
      push(4, to_lp_reg);
      break;
    default:
      push(args->ty->size, to_gp_reg);
      break;
  }
}

static int push_args(Node *node) {
  int stack = 0, gp = 0, fp = 0, dp = 0, lp = 0;

  // If the return type is a large struct/union, the caller passes
  // a pointer to a buffer as if it were the first argument.
  if (node->ret_buffer)
    gp++;

  // Load as many arguments to the registers as possible.
  for (Node *arg = node->args; arg; arg = arg->next) {
    Type *ty = arg->ty;
    
    switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        arg->pass_by_stack = true;
        stack += align_to(ty->size, ty->align);
        break;
      case TY_FLOAT:
        if (fp++ >= FP_MAX) {
          arg->pass_by_stack = true;
          stack += ty->align;
        }
        break;
      case TY_DOUBLE:
        if (dp++ >= DP_MAX) {
          arg->pass_by_stack = true;
          stack += ty->align;
        }
        break;
      case TY_LONG:
        if (lp++ >= LP_MAX) {
          arg->pass_by_stack = true;
          stack += ty->align;
        }
        break;
      case TY_ARRAY:
        if (gp++ >= GP_MAX) {
          arg->pass_by_stack = true;
          stack += 4;
        }
        break;
      default:
        if (gp++ >= GP_MAX) {
          arg->pass_by_stack = true;
          stack += ty->align;
        }
        break;
    }
  }
  
  push_args2(node->args, true);
  push_args2(node->args, false);
  
  // If the return type is a large struct/union, the caller passes
  // a pointer to a buffer as if it were the first argument.
  if (node->ret_buffer) {
    println("\tlea p0, @p6+%d", node->ret_buffer->offset);
    push(3, 0);
  }
  
  return align_to(stack, 2);
}

static void copy_struct(int from_ptr) {
  Type *ty = current_fn->ty->return_ty;
  Obj *var = current_fn->params;
  
  if (from_ptr == 0) return;
  println("\tld.p p0, @p6+%d", var->offset);
  
  for (int i = 0; i < ty->size; i += 2) {
    println("\tld.w @p0+, @p%d+", from_ptr);
  }
}

static void builtin_alloca(int to_reg) {
  int c = count();
  
  // Save P1 so it doesn't get clobbered
  println("\tld.p @-sp, p1");
  
  // Align size to 2 bytes
  println("\tadq.p p%d, 1", to_reg);
  println("\tand.p p%d, $fffffe", to_reg);
  
  // Shift the temporary area
  println("\tld.p p0, sp");
  println("\tsub.p sp, p%d", to_reg);
  println("\tld.p p1, sp");
  println("__L_alloca_%d:", c);
  println("\tcp.p p0, sp");
  println("\tjr eq, __L_allocabreak_%d", c);
  println("\tld.b @p1+, @p0+");
  println("\tjr.s __L_alloca_%d", c);
  println("__L_allocabreak_%d:", c);
  
  // Restore P1
  println("\tld.p p1, @sp+");
  
  // Move alloca_bottom pointer
  println("\tld.p p0, @p6+%d", current_fn->alloca_bottom->offset);
  println("\tsub.p p0, p%d", to_reg);
  println("\tld.p @p6+%d, p0", current_fn->alloca_bottom->offset);
}

static int get_reg_type(Type *ty) {
  if (ty->kind == TY_LONG || ty->kind == TY_ENUM)
    return to_lp_reg;
  else if (ty->kind == TY_FLOAT)
    return to_fp_reg;
  else if (ty->kind == TY_DOUBLE)
    return to_dp_reg;
  else
    return to_gp_reg;
}

// Generate code for a given node.
// The collapse parameter tells gen_expr to use the current register instead of the next one.
// Returns true when the register index should be decremented.
static bool gen_expr(Node *node, bool collapse, bool override) {
  //println("\t; .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  int rec_reg;
  int to_reg;
  
  indents++;
  
  bool ret = false;
  
  if (node->kind != ND_NULL_EXPR && node->kind != ND_MEMZERO) {
    Type *ty = node->ty;
    
    if (override) {
      to_reg = 0;
      rec_reg = 0;
    }
    else if (ty->kind == TY_FLOAT) {
      rec_reg = MIN(to_fp_reg + 1, FP_MAX - 1);
      to_reg = to_fp_reg;
      if (!collapse) {
        to_fp_reg = rec_reg;
        ret = true;
      }
    }
    else if (ty->kind == TY_DOUBLE) {
      rec_reg = MIN(to_dp_reg + 1, DP_MAX - 1);
      to_reg = to_dp_reg;
      if (!collapse) {
        to_dp_reg = rec_reg;
        ret = true;
      }
    }
    else if (ty->kind == TY_LONG || ty->kind == TY_ENUM) {
      rec_reg = MIN(to_lp_reg + 1, LP_MAX - 1);
      to_reg = to_lp_reg;
      if (!collapse) {
        to_lp_reg = rec_reg;
        ret = true;
      }
    }
    else {
      rec_reg = MIN(to_gp_reg + 1, GP_SCRATCH_END - 1);
      to_reg = to_gp_reg;
      if (!collapse) {
        to_gp_reg = rec_reg;
        ret = true;
      }
    }
  }
  
  debug("%d@%s:%d", node->kind, node->tok->file->name, node->tok->line_no);
  
  switch (node->kind) {
    case ND_NULL_EXPR:
      indents--; return ret;
    case ND_NUM: {
      switch (node->ty->kind) {
        case TY_FLOAT: {
          union { float f32; uint32_t u32; } u = { node->fval };
          println("\tld.w w0, %04hx ; float %Lf", (uint16_t)(u.u32 & 0xffff), node->fval);
          println("\tld.w @__float_%d0, w0", to_reg);
          println("\tld.w w0, %04hx", (uint16_t)(u.u32 >> 16));
          println("\tld.w @__float_%d1, w0", to_reg);
          indents--; return ret;
        }
        case TY_DOUBLE: {
          union { double f64; uint64_t u64; } u = { node->fval };
          println("\tld.w w0, $%04hx ; double %Lf", (uint16_t)(u.u64 & 0xffff), node->fval);
          println("\tld.w @__double_%d0, w0", to_reg);
          println("\tld.w w0, $%04hx", (uint16_t)((u.u64 >> 16) & 0xffff));
          println("\tld.w @__double_%d1, w0", to_reg);
          println("\tld.w w0, $%04hx", (uint16_t)((u.u64 >> 32) & 0xffff));
          println("\tld.w @__double_%d2, w0", to_reg);
          println("\tld.w w0, $%04hx", (uint16_t)(u.u64 >> 48));
          println("\tld.w @__double_%d3, w0", to_reg);
          indents--; return ret;
        }
        case TY_LONG:
        case TY_ENUM:
          if (node->ty->is_unsigned)
            println("\tld.w w0, $%04hx ; long %u", (uint16_t)(node->val & 0xffff), (uint32_t)(node->val));
          else
            println("\tld.w w0, $%04hx ; long %d", (uint16_t)(node->val & 0xffff), (int32_t)(node->val));
          println("\tld.w @__long_%d0, w0", to_reg);
          println("\tld.w w0, $%04hx", (uint16_t)(node->val >> 16));
          println("\tld.w @__long_%d1, w0", to_reg);
          indents--; return ret;
        default: {
          if (node->val < 128 && node->val > -129)
            println("\tldq p%d, %d", to_reg, (int8_t)(node->val & 0xff));
          else
            println("\tld.%c %c%d, %d", get_suffix(node->ty->size), get_stack_reg(node->ty->size), to_reg, (int32_t)(node->val & 0xffffff));
          indents--; return ret;
        }
      }
    }
    case ND_NEG:
      gen_expr(node->lhs, true, false);
      switch (node->ty->kind) {
        case TY_FLOAT:
          println("\tld.w w0, $8000");
          println("\txor.w @__float_%d1, w0", to_reg);
          indents--; return ret;
        case TY_DOUBLE:
          println("\tld.w w0, $8000");
          println("\txor.w @__double_%d3, w0", to_reg);
          indents--; return ret;
        case TY_LONG:
        case TY_ENUM:
          println("\tneg.w @__long_%d0", to_reg);
          println("\tngx.w @__long_%d1", to_reg);
          indents--; return ret;
        default:
          println("\tneg.%c %c%d", get_suffix(node->ty->size), get_stack_reg(node->ty->size), to_reg);
          indents--; return ret;
      }
    case ND_VAR: {
      if (node->ty->size <= 3) {
        char *insn = node->ty->is_unsigned ? "ldzx" : "ldsx";
        char suffix = get_suffix(node->ty->size);
        
        if (node->var->is_local) {
          if (node->ty->size == 1)
            println("\t%s.%c p%d, @p6+%d", insn, suffix, to_reg, node->var->offset);
          else if (node->ty->size == 2)
            println("\t%s.%c p%d, @p6+%d", insn, suffix, to_reg, node->var->offset);
          else
            println("\tld.%c p%d, @p6+%d", suffix, to_reg, node->var->offset);
        }
        else {
          if (node->ty->size == 1)
            println("\t%s.%c p%d, %s", insn, suffix, to_reg, node->var->name);
          else if (node->ty->size == 2)
            println("\t%s.%c p%d, %s", insn, suffix, to_reg, node->var->name);
          else
            println("\tld.%c p%d, %s", suffix, to_reg, node->var->name);
        }
      }
      else if (node->ty->kind == TY_FLOAT) {
        println("\tld.w @__float_%d0, @p6+%d", to_reg, node->var->offset);
        println("\tld.w @__float_%d1, @p6+%d", to_reg, node->var->offset + 2);
      }
      else if (node->ty->kind == TY_DOUBLE) {
        println("\tld.w @__double_%d0, @p6+%d", to_reg, node->var->offset);
        println("\tld.w @__double_%d1, @p6+%d", to_reg, node->var->offset + 2);
        println("\tld.w @__double_%d2, @p6+%d", to_reg, node->var->offset + 4);
        println("\tld.w @__double_%d3, @p6+%d", to_reg, node->var->offset + 6);
      }
      else if (node->ty->kind == TY_LONG || node->ty->kind == TY_ENUM) {
        println("\tld.w @__long_%d0, @p6+%d", to_reg, node->var->offset);
        println("\tld.w @__long_%d1, @p6+%d", to_reg, node->var->offset + 2);
      }
      else {
        gen_addr(node, rec_reg);
        load(node->var->ty, to_reg, rec_reg);
      }
      
      indents--; return ret;
    }
    case ND_MEMBER: {
      gen_addr(node, rec_reg);
      load(node->ty, to_reg, rec_reg);
      
      Member *mem = node->member;
      if (mem->is_bitfield) {
        int sz = (mem->bit_width + 8) / 8;
        
        for (int i = 0; i < sz - mem->bit_width - mem->bit_offset; i++) {
          if (sz <= 3) {
            char suffix = get_suffix(sz);
            char reg = get_stack_reg(sz);
            println("\tsla.%c %c%d", suffix, reg, to_reg);
          }
          else {
            println("\tsla.w @__long_%d1", to_reg);
            println("\trl.w @__long_%d0", to_reg);
          }
        }
        
        char *insn = mem->ty->is_unsigned ? "srl" : "sra";
        for (int i = 0; i < sz - mem->bit_width; i++) {
          if (sz <= 3) {
            char suffix = get_suffix(sz);
            char reg = get_stack_reg(sz);
            println("\t%s.%c %c%d", insn, suffix, reg, to_reg);
          }
          else {
            println("\t%s.w @__long_%d1", insn, to_reg);
            println("\trr.w @__long_%d0", to_reg);
          }
        }
      }
      indents--; return ret;
    }
    case ND_DEREF: {
      if (gen_expr(node->lhs, false, false)) {
        if (node->lhs->ty->kind == TY_FLOAT)
          to_fp_reg--;
        else if (node->lhs->ty->kind == TY_DOUBLE)
          to_dp_reg--;
        else if (node->lhs->ty->kind == TY_LONG || node->lhs->ty->kind == TY_ENUM)
          to_lp_reg--;
        else
          to_gp_reg--;
      }
      load(node->ty, to_reg, rec_reg);
      indents--; return ret;
    }
    case ND_ADDR:
      gen_addr(node->lhs, to_reg);
      indents--; return ret;
    case ND_ASSIGN:
      gen_addr(node->lhs, to_reg);
      if (to_reg == rec_reg) push(3, to_reg);
      if (gen_expr(node->rhs, false, false)) {
        ret = false;
        if (node->rhs->ty->kind == TY_FLOAT)
          to_fp_reg--;
        else if (node->rhs->ty->kind == TY_DOUBLE)
          to_dp_reg--;
        else if (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM)
          to_lp_reg--;
        else
          to_gp_reg--;
      }
      
      if (node->lhs->kind == ND_MEMBER && node->lhs->member->is_bitfield) {
        // If the lhs is a bitfield, we need to read the current value
        // from memory and merge it with a new value.
        Member *mem = node->lhs->member;
        int sz = (mem->bit_width + 7) / 8;
        
        if (sz <= 3) {
          if (sz == 1) sz = 2;
          char suffix = get_suffix(sz);
          char reg = get_stack_reg(sz);
          
          println("\tand.%c %c%d, %u", suffix, reg, rec_reg, (uint32_t)(((1L << mem->bit_width) - 1) & 0xffffff));
          for (int i = 0; i < mem->bit_offset; i++) {
            println("\tsla.%c %c%d", suffix, reg, rec_reg);
          }
          println("\tld.%c @-sp, %c%d", suffix, reg, rec_reg);
          
          // load the offset pointer we might've pushed to begin with
          if (to_reg == rec_reg)
            println("\tld.p p%d, @sp+%d", to_reg, sz == 3 ? 4 : sz);
          load(mem->ty, rec_reg, to_reg);
          
          println("\tand.%c %c%d, %u", suffix, reg, rec_reg, (uint32_t)(~(((1L << mem->bit_width) - 1) << mem->bit_offset)) & 0xffffff);
          println("\tor.%c %c%d, @sp+", suffix, reg, rec_reg);
          
          store(node->ty, to_reg == rec_reg ? -1 : to_reg, rec_reg);
          indents--; return ret;
        }
        else {
          // save previous values
          println("\tld.p @-sp, p0");
          println("\tld.p @-sp, p1");
          
          println("\tld.w w0, @__long_%d0", rec_reg);
          println("\tld.w w1, @__long_%d1", rec_reg);
          
          int mask = ((1L << mem->bit_width) - 1);
          println("\tand.w w0, %hu", (uint16_t)(mask & 0xffff));
          println("\tand.w w1, %hu", (uint16_t)(mask >> 16));
          for (int i = 0; i < mem->bit_offset; i++) {
            println("\tsla.w w0");
            println("\trl.w w1");
          }
          
          if (to_reg == rec_reg) {
            println("\tld.w @-sp, w1");
            println("\tld.w @-sp, w0");
            println("\tld.p p1, @sp+16");
          }
          else {
            println("\tld.w @__long_%d0, w0", rec_reg);
            println("\tld.w @__long_%d1, w1", rec_reg);
            println("\tld.p p1, @sp+8");
          }
          load(mem->ty, rec_reg, 1);
          
          uint32_t mask2 = ~(((1L << mem->bit_width) - 1) << mem->bit_offset);
          println("\tand.w @__long_%d0, %hu", rec_reg, (uint16_t)(mask2 & 0xffff));
          println("\tand.w @__long_%d1, %hu", rec_reg, (uint16_t)(mask2 >> 16));
          
          println("\tld.w w0, @__long_%d0", rec_reg);
          println("\tld.w w1, @__long_%d1", rec_reg);
          if (to_reg == rec_reg) {
            println("\tor.w w0, @sp+");
            println("\tor.w w1, @sp+");
          }
          else {
            println("\tor.w w0, @__long_%d0", rec_reg);
            println("\tor.w w1, @__long_%d1", rec_reg);
          }
          
          println("\tld.w @__long_%d0, w0", rec_reg);
          println("\tld.w @__long_%d1, w1", rec_reg);
          
          // restore previous values so that the offset pointer is on top
          println("\tld.p p1, @sp+");
          println("\tld.p p0, @sp+");
          
          store(node->ty, to_reg == rec_reg ? -1 : to_reg, rec_reg);
          indents--; return ret;
        }
      }
      
      store(node->ty, to_reg == rec_reg ? -1 : to_reg, rec_reg);
      indents--; return ret;
    case ND_STMT_EXPR:
      for (Node *n = node->body; n; n = n->next)
        gen_stmt(n);
      indents--; return ret;
    case ND_COMMA:
      gen_expr(node->lhs, true, false);
      gen_expr(node->rhs, true, false);
      indents--; return ret;
    case ND_CAST:
      gen_expr(node->lhs, false, false);
      cast(node->lhs->ty, node->ty, get_reg_type(node->lhs->ty), to_reg);
      indents--; return ret;
    case ND_MEMZERO: {
      println("\tlea p0, @p6+%d", node->var->offset);
      if (node->var->ty->size <= 32) {
        println("\trepi %d", node->var->ty->size);
        println("\tld.b @p0+, 0");
        indents--; return ret;
      }
      else {
        int c = count();
        println("\tld.p @-sp, p1");
        println("\tld.p p0, %d", node->var->ty->size);
        println("__L_zeroize_%d:", c);
        println("\tcp.p p1, 0");
        println("\tjr eq, __L_zeroizebreak_%d", c);
        println("\tld.b @p0+, 0");
        println("\tdjnz p1, __L_zeroize_%d", c);
        println("__L_zeroizebreak_%d:", c);
        println("\tld.p p1, @sp+");
        indents--; return ret;
      }
    }
    case ND_COND: {
      int c = count();
      gen_expr(node->cond, true, false);
      cmp_zero(node->cond->ty, get_reg_type(node->cond->ty));
      println("\tjr ne, __L_then_%d", c);
      println("\tjr.l __L_else_%d", c);
      println("__L_then_%d:", c);
      gen_expr(node->then, true, false);
      println("\tjr.l __L_end_%d", c);
      println("__L_else_%d:", c);
      gen_expr(node->els, true, false);
      println("__L_end_%d:", c);
      indents--; return ret;
    }
    case ND_NOT: {
      int c = count();
      gen_expr(node->lhs, true, false);
      cmp_zero(node->lhs->ty, get_reg_type(node->lhs->ty));
      println("\tjr eq, __L_not_%d", c);
      println("\tldq p%d, $01", to_reg);
      println("\tjr.s __L_notnot_%d", c);
      println("__L_not_%d:", c);
      println("\tldq p%d, $00", to_reg);
      println("__L_notnot_%d:", c);
      indents--; return ret;
    }
    case ND_BITNOT:
      gen_expr(node->lhs, true, false);
      if (node->ty->kind == TY_LONG || node->ty->kind == TY_ENUM) {
        println("\tcpl.w @__long_%d0", to_reg);
        println("\tcpl.w @__long_%d1", to_reg);
      }
      else {
        println("\tcpl.%c %c%d", get_suffix(node->ty->size), get_stack_reg(node->ty->size), to_reg);
      }
      indents--; return ret;
    case ND_LOGAND: {
      int c = count();
      gen_expr(node->lhs, true, false);
      cmp_zero(node->lhs->ty, get_reg_type(node->lhs->ty));
      println("\tjr nz, __L_true_%d", c);
      println("\tjr.l __L_false_%d", c);
      println("__L_true_%d:", c);
      gen_expr(node->rhs, true, false);
      cmp_zero(node->rhs->ty, get_reg_type(node->rhs->ty));
      println("\tjr z, __L_false_%d", c);
      println("\tldq p%d, $00", to_reg);
      println("\tjr.s __L_end_%d", c);
      println("__L_false_%d:", c);
      println("\tldq p%d, $01", to_reg);
      println("__L_end_%d:", c);
      indents--; return ret;
    }
    case ND_LOGOR: {
      int c = count();
      gen_expr(node->lhs, true, false);
      cmp_zero(node->lhs->ty, get_reg_type(node->lhs->ty));
      println("\tjr z, __L_false_%d", c);
      println("\tjr.l __L_true_%d", c);
      println("__L_false_%d:", c);
      gen_expr(node->rhs, true, false);
      cmp_zero(node->rhs->ty, get_reg_type(node->rhs->ty));
      println("\tjr nz, __L_true_%d", c);
      println("\tldq p%d, $00", to_reg);
      println("\tjr.s __L_end_%d", c);
      println("__L_true_%d:", c);
      println("\tldq p%d, $01", to_reg);
      println("__L_end_%d:", c);
      indents--; return ret;
    }
    case ND_FUNCALL: {
      if (node->lhs->kind == ND_VAR && !strcmp(node->lhs->var->name, "alloca")) {
        gen_expr(node->args, true, false);
        builtin_alloca(to_reg);
        indents--; return ret;
      }
      
      int stack_args = push_args(node);
      if (node->lhs->kind != ND_VAR || node->lhs->var->is_local) {
        if (gen_expr(node->lhs, false, false)) {
          if (node->lhs->ty->kind == TY_FLOAT)
            to_fp_reg--;
          else if (node->lhs->ty->kind == TY_DOUBLE)
            to_dp_reg--;
          else if (node->lhs->ty->kind == TY_LONG || node->lhs->ty->kind == TY_ENUM) {
            to_lp_reg--;
          }
          else
            to_gp_reg--;
        }
      }
      
      int gp = 0, fp = 0, dp = 0, lp = 0;
      
      // If the return type is a large struct/union, the caller passes
      // a pointer to a buffer as if it were the first argument.
      if (node->ret_buffer)
        pop(3, ++gp);

      for (Node *arg = node->args; arg; arg = arg->next) {
        Type *ty = arg->ty;
        
        switch (ty->kind) {
          case TY_STRUCT:
          case TY_UNION:
            continue;
          case TY_FLOAT:
            if (fp < FP_MAX)
              popf(ty->size, fp++);
            break;
          case TY_DOUBLE:
            if (dp < DP_MAX)
              popf(ty->size, dp++);
            break;
          case TY_LONG:
          case TY_ENUM:
            if (lp < LP_MAX)
              pop(ty->size, lp++);
            break;
          default:
            if (gp < GP_MAX)
              pop(ty->size, ++gp);
            break;
        }
      }
      
      // make sure we're on a word boundary
      if (depth % 2 == 1) {
        println("\tsbq.p sp, 1");
        depth++;
      }
      
      if (node->lhs->kind == ND_VAR && !node->lhs->var->is_local)
        println("\tcall %s", node->lhs->var->name);
      else
        println("\tcall p%d", rec_reg);
      
      if (stack_args > 0 && stack_args <= 8)
        println("\tadq.p sp, %d", stack_args);
      else if (stack_args > 0)
        println("\tadd.p sp, %d", stack_args);

      depth -= stack_args;
      
      // It looks like the most significant bits in P0 may
      // contain garbage if a function return type is short or bool/char,
      // respectively. We clear the upper bits here.
      switch (node->ty->kind) {
        case TY_VOID:
          indents--; return ret;
        case TY_BOOL:
          println("\tldzx.b p%d, l0", to_reg);
          indents--; return ret;
        case TY_CHAR:
          if (node->ty->is_unsigned)
            println("\tldzx.b p%d, l0", to_reg);
          else
            println("\tldsx.b p%d, l0", to_reg);
          indents--; return ret;
        case TY_SHORT:
          if (node->ty->is_unsigned)
            println("\tldzx.w p%d, w0", to_reg);
          else
            println("\tldsx.w p%d, w0", to_reg);
          indents--; return ret;
        case TY_LONG:
        case TY_ENUM: {
          if (to_reg != 0) {
            println("\tld.w @__long_%d0, @__long_00", to_reg);
            println("\tld.w @__long_%d1, @__long_01", to_reg);
          }
          indents--; return ret;
        }
        case TY_FLOAT: {
          if (to_reg != 0) {
            println("\tld.w @__float_%d0, @__float_00", to_reg);
            println("\tld.w @__float_%d1, @__float_01", to_reg);
          }
          indents--; return ret;
        }
        case TY_DOUBLE: {
          if (to_reg != 0) {
            println("\tld.w @__double_%d0, @__double_00", to_reg);
            println("\tld.w @__double_%d1, @__double_01", to_reg);
            println("\tld.w @__double_%d2, @__double_02", to_reg);
            println("\tld.w @__double_%d3, @__double_03", to_reg);
          }
          indents--; return ret;
        }
        default:
          if (to_reg != 0)
            println("\tld.p p%d, p0", to_reg);
          indents--; return ret;
      }
    }
    case ND_LABEL_VAL:
      println("\tlea p%d, @%s", to_reg, node->unique_label);
      indents--; return ret;
    default:
      break;
  }

  switch (node->ty->kind) {
    case TY_FLOAT:
    case TY_DOUBLE: {
      gen_expr(node->lhs, true, false);
      if (node->ty->kind == TY_DOUBLE) {
        println("ld.w @__softfp_tmp00, @__double_%d0", to_reg);
        println("ld.w @__softfp_tmp01, @__double_%d1", to_reg);
        println("ld.w @__softfp_tmp02, @__double_%d2", to_reg);
        println("ld.w @__softfp_tmp03, @__double_%d3", to_reg);
      }
      else {
        println("ld.w @__softfp_tmp00, @__float_%d0", to_reg);
        println("ld.w @__softfp_tmp01, @__float_%d1", to_reg);
      }
      gen_expr(node->rhs, true, false);
      if (node->ty->kind == TY_DOUBLE) {
        println("ld.w @__softfp_tmp10, @__double_%d0", to_reg);
        println("ld.w @__softfp_tmp11, @__double_%d1", to_reg);
        println("ld.w @__softfp_tmp12, @__double_%d2", to_reg);
        println("ld.w @__softfp_tmp13, @__double_%d3", to_reg);
      }
      else {
        println("ld.w @__softfp_tmp10, @__float_%d0", to_reg);
        println("ld.w @__softfp_tmp11, @__float_%d1", to_reg);
      }
      
      char *sz = node->ty->kind == TY_FLOAT ? "sf" : "df";

      switch (node->kind) {
        case ND_ADD:
          println("\tcall __add%s3", sz);
          indents--; return ret;
        case ND_SUB:
          println("\tcall __sub%s3", sz);
          indents--; return ret;
        case ND_MUL:
          println("\tcall __mul%s3", sz);
          indents--; return ret;
        case ND_DIV:
          println("\tcall __div%s3", sz);
          indents--; return ret;
        case ND_EQ:
        case ND_NE:
        case ND_LT:
        case ND_LE:
          if (node->kind == ND_EQ) {
            println("\tcall __eq%s2", sz);
          } else if (node->kind == ND_NE) {
            println("\tcall __ne%s2", sz);
          } else if (node->kind == ND_LT) {
            println("\tcall __lt%s2", sz);
          } else {
            println("\tcall __le%s2", sz);
          }
          println("\tand.b l0, $01");
          println("\tldzx.b p%d, l0", to_reg);
          indents--; return ret;
        default:
          error_tok(node->tok, "invalid expression");
          indents--; return ret;
      }
    }
    default:
      break;
  }

  gen_expr(node->lhs, true, false);
  int pop_reg = get_reg_type(node->lhs->ty);
  if (to_reg == rec_reg) {
    push(node->lhs->ty->size, pop_reg);
  }
  gen_expr(node->rhs, true, false);
  
  if (node->ty->kind == TY_LONG || node->ty->kind == TY_ENUM) {
    if (to_reg == rec_reg && (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM)) {
      // usual arithmetic conversion: use long 2 as a temporary source
      println("\tld.p @__long_20, @__long_%d0", rec_reg);
      println("\tld.p @__long_21, @__long_%d1", rec_reg);
      rec_reg = 2;
      
      pop(node->lhs->ty->size, pop_reg);
    }
    else if (node->rhs->ty->kind != TY_LONG && node->rhs->ty->kind != TY_ENUM && (node->kind == ND_SHL || node->kind == ND_SHR)) {
      // shift instructions: use the next GP register as the shift count
      if (to_reg == rec_reg) {
        pop(node->lhs->ty->size, pop_reg);
      }
    }
    
    switch (node->kind) {
      case ND_ADD:
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tadd.w @__long_%d0, w0", to_reg);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tadx.w @__long_%d1, w0", to_reg);
        indents--; return ret;
      case ND_SUB:
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tsub.w @__long_%d0, w0", to_reg);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tsbx.w @__long_%d1, w0", to_reg);
        indents--; return ret;
      case ND_MUL:
        println("\tld.w @-sp, w1");
        
        // compute partial product #1 (bits 0-15)
        println("\tld.w w1, @__long_%d0", to_reg);
        println("\tmulu.w w1, @__long_%d0", rec_reg);
        println("\tld.w @-sp, w1");
        println("\tld.w @-sp, w0");
        println("\tld.w w1, @__long_%d1", to_reg);
        if (node->ty->is_unsigned)
          println("\tmulu.w w1, @__long_%d0", rec_reg);
        else
          println("\tmuls.w w1, @__long_%d0", rec_reg);
        println("\tadd.w @sp+2, w1");
        
        // add truncated partial product #2 (bits 16-31)
        println("\tld.w w1, @__long_%d0", to_reg);
        println("\tmulu.w w1, @__long_%d1", rec_reg);
        println("\tadd.w @sp, w1");
        
        // transfer the product back to the source
        println("\tld.w @__long_%d0, @sp+", to_reg);
        println("\tld.w @__long_%d1, @sp+", to_reg);
        
        println("\tld.w w1, @sp+");
        indents--; return ret;
      case ND_DIV:
      case ND_MOD: {
        int c = count();
        println("\tld.w @-sp, w1");
        println("\tldq p0, $00");
        
        // bit 23 of P0 is used to mark whether to negate the result
        if (!(node->ty->is_unsigned)) {
          println("\tcp.w @__long_%d1, 0", rec_reg);
          println("\tjr p, __L_divskipnega_%d", c);
          println("\tneg.w @__long_%d0", rec_reg);
          println("\tngx.w @__long_%d1", rec_reg);
          println("\txor.p p0, $800000");
          println("__L_divskipnegx_%d:", c);
          
          println("\tcp.w @__long_%d1, 0", to_reg);
          println("\tjr p, __L_divskipnegb_%d", c);
          println("\tneg.w @__long_%d0", to_reg);
          println("\tngx.w @__long_%d1", to_reg);
          println("\txor.p p0, $800000");
          println("__L_divskipnegy_%d:", c);
        }
        
        // check if the top half of the divisor is zero
        // (if it is, we can shortcut to the DIVU.W instruction)
        println("\tcp.w @__long_%d1, 0", rec_reg);
        println("\tjr z, __L_divzero_%d", c);
        
        // do software 32 bit / 32 bit division (http://www.piclist.com/techref/microchip/math/div/div16or32by16to16.htm)
        // initialize loop counter (P4) and remainder registers (W0, W1), save W2 and W3 for quotient
        println("\tld.w @-sp, w3");
        println("\tld.w @-sp, w2");
        println("\tld.p @-sp, p4");
        println("\tld.w w1, 0");
        println("\tldq p4, 32");
        
        println("__L_divloop_%d:", c);
        
        // rotate remainder:dividend left
        println("\tsla.w @__long_%d0", to_reg);
        println("\trl.w @__long_%d1", to_reg);
        println("\trl.w w0");
        println("\trl.w w1");
        
        // subtract divisor from remainder
        println("\tsub.w w0, @__long_%d0", rec_reg);
        println("\tsbx.w w1, @__long_%d1", rec_reg);
        
        // invert borrow to produce carry
        println("\txor.b f, $01");
        
        // shift the quotient bit in
        println("\trl.w w2");
        println("\trl.w w3");
        
        // jump back if the loop isn't done
        println("\tdjnz p4, __L_divloop_%d", c);
        
        // place the remainder in to_reg
        println("\tld.w @__long_%d0, w0", to_reg);
        println("\tld.w @__long_%d1, w1", to_reg);
        
        // push the quotient and restore W2 and W3
        println("\tld.w w0, @sp+");
        println("\tld.w w1, @sp+");
        println("\tld.w @-sp, w3");
        println("\tld.w @-sp, w2");
        println("\tld.w w2, w0");
        println("\tld.w w3, w1");
        
        println("\tld.w w2, @sp+");
        println("\tld.w w3, @sp+");
        println("\tld.p p4, @sp+");
        println("\tjr.s __L_divnonzero_%d", c);
        
        // if the upper half was zero, defer division to the lower half
        // (quotient = 0, remainder = upper half)
        println("__L_divzero_%d:", c);
        println("\tld.w w0, @__long_%d1", to_reg);
        println("\tld.w @-sp, 0");
        
        // compute partial quotient #1 (bits 0-15)
        // this will raise the divide-by-zero exception if the dividend is zero
        println("\tld.w w1, @__long_%d0", to_reg);
        println("\tdivu.w w1, @__long_%d0", rec_reg);
        println("\tld.w @-sp, w1");
        println("\tld.w @__long_%d0, w0", to_reg);
        
        // after that long chunk of code, the quotient is on the stack and the remainder is in to_reg
        println("__L_divnonzero_%d:", c);
        if (node->kind == ND_DIV) {
          println("\tld.w @__long_%d0, @sp+", to_reg);
          println("\tld.w @__long_%d1, @sp+", to_reg);
        }
        else {
          println("\tadq.p sp, 4");
        }
        
        if (!(node->ty->is_unsigned)) {
          println("\tcp.p p0, 0");
          println("\tjr p, __L_divskipnegq_%d", c);
          println("\tneg.w @__long_%d0", to_reg);
          println("\tngx.w @__long_%d1", to_reg);
          println("__L_divskipnegq_%d:", c);
        }
        
        println("\tld.w w1, @sp+");
        indents--; return ret;
      }
      case ND_BITAND:
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tand.w @__long_%d0, w0", to_reg);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tand.w @__long_%d1, w0", to_reg);
        break;
      case ND_BITOR:
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tor.w @__long_%d0, w0", to_reg);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tor.w @__long_%d1, w0", to_reg);
        break;
      case ND_BITXOR:
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\txor.w @__long_%d0, w0", to_reg);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\txor.w @__long_%d1, w0", to_reg);
        break;
      case ND_EQ: {
        int c = count();
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tcp.w w0, @__long_%d0", to_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tcp.w w0, @__long_%d1", to_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tldq p%d, $01", to_reg);
        println("\tjr.s __L_eq_%d", c);
        println("__L_ne_%d:", c);
        println("\tldq p%d, $00", to_reg);
        println("__L_eq_%d:", c);
        indents--; return ret;
      }
      case ND_NE: {
        int c = count();
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tcp.w w0, @__long_%d0", to_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tcp.w w0, @__long_%d1", to_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_eq_%d", c);
        println("__L_ne_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_eq_%d:", c);
        indents--; return ret;
      }
      case ND_LT: {
        int c = count();
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tcp.w w0, @__long_%d1", to_reg);
        if (node->lhs->ty->is_unsigned)
          println("\tjr ult, __L_lt_%d", c);
        else
          println("\tjr lt, __L_lt_%d", c);
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tcp.w w0, @__long_%d0", to_reg);
        println("\tjr ult, __L_lt_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_ge_%d", c);
        println("__L_lt_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_ge_%d:", c);
        indents--; return ret;
      }
      case ND_LE: {
        int c = count();
        println("\tld.w w0, @__long_%d1", rec_reg);
        println("\tcp.w w0, @__long_%d1", to_reg);
        if (node->lhs->ty->is_unsigned)
          println("\tjr ule, __L_le_%d", c);
        else
          println("\tjr le, __L_le_%d", c);
        println("\tld.w w0, @__long_%d0", rec_reg);
        println("\tcp.w w0, @__long_%d0", to_reg);
        println("\tjr ule, __L_le_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_gt_%d", c);
        println("__L_le_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_gt_%d:", c);
        indents--; return ret;
      }
      case ND_SHL: {
        int c = count();
        if (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM) {
          println("\tld.w @-sp, w1");
          println("\tld.w w0, @__long_%d0", rec_reg);
          println("\tld.w w1, @__long_%d1", rec_reg);
          println("__L_shl_%d:", c);
          println("\tsub.w w0, 1");
          println("\tsbx.w w1, 0");
        }
        else {
          println("__L_shl_%d:", c);
          println("\tsbq.%c %c%d, 1", get_suffix(node->rhs->ty->size), get_stack_reg(node->rhs->ty->size), to_gp_reg);
        }
        
        println("\tsla.w @__long_%d0", to_reg);
        println("\trl.w @__long_%d1", to_reg);
        
        if (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM) {
          println("\tcp.w w0, 0");
          println("\tjr ne, __L_shl_%d", c);
          println("\tcp.w w1, 0");
          println("\tjr ne, __L_shl_%d", c);
          println("\tld.w w1, @sp+");
        }
        else {
          println("\tcp.%c %c%d, 0", get_suffix(node->rhs->ty->size), get_stack_reg(node->rhs->ty->size), to_gp_reg);
          println("\tjr ne, __L_shl_%d", c);
        }
        indents--; return ret;
      }
      case ND_SHR:{
        int c = count();
        if (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM) {
          println("\tld.w @-sp, w1");
          println("\tld.w w0, @__long_%d0", rec_reg);
          println("\tld.w w1, @__long_%d1", rec_reg);
          println("__L_shr_%d:", c);
          println("\tsub.w w0, 1");
          println("\tsbx.w w1, 0");
        }
        else {
          println("__L_shr_%d:", c);
          println("\tsbq.%c %c%d, 1", get_suffix(node->rhs->ty->size), get_stack_reg(node->rhs->ty->size), to_gp_reg);
        }
        if (node->lhs->ty->is_unsigned)
          println("\tsra.w @__long_%d1", to_reg);
        else
          println("\tsrl.w @__long_%d1", to_reg);
        println("\trr.w @__long_%d0", to_reg);
        
        if (node->rhs->ty->kind == TY_LONG || node->rhs->ty->kind == TY_ENUM) {
          println("\tcp.w w0, 0");
          println("\tjr ne, __L_shr_%d", c);
          println("\tcp.w w1, 0");
          println("\tjr ne, __L_shr_%d", c);
          println("\tld.w w1, @sp+");
        }
        else {
          println("\tcp.%c %c%d, 0", get_suffix(node->rhs->ty->size), get_stack_reg(node->rhs->ty->size), to_gp_reg);
          println("\tjr ne, __L_shr_%d", c);
        }
        indents--; return ret;
      }
      default:
        break;
    }
    indents--; return ret;
  } 
  else {
    char suffix = get_suffix(node->ty->size);
    char reg = get_stack_reg(node->ty->size);
    
    if (to_reg == rec_reg) {
      if (node->kind != ND_MUL && node->kind != ND_DIV && node->kind != ND_MOD) {
        // use p0 as a temporary source
        println("\tld.p p0, p%d", rec_reg);
        rec_reg = 0;
        pop(node->lhs->ty->size, pop_reg);
      }
      else {
        // use P1 as a temporary source (can't use P0)
        println("\tld.p @-sp, p1");
        println("\tld.p p1, p%d", rec_reg);
        rec_reg = 1;
        
        // we can't call pop() since the stack is funky at this point
        if (node->ty->size == 1) {
          suffix = get_suffix(2);
          reg = get_stack_reg(2);
        }
        println("\tld.%c %c%d, @sp+4", suffix, reg, pop_reg);
        depth -= node->lhs->ty->align;
      }
    }
    
    switch (node->kind) {
      case ND_ADD:
        println("\tadd.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        indents--; return ret;
      case ND_SUB:
        println("\tsub.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        indents--; return ret;
      case ND_MUL:
        if (node->ty->is_unsigned)
          println("\tmulu.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        else
          println("\tmuls.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        println("\tld.p p1, @sp+");
        indents--; return ret;
      case ND_DIV:
      case ND_MOD:
        println("\tldq p0, $00");
        if (node->ty->is_unsigned)
          println("\tdivu.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        else
          println("\tdivs.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        if (node->kind == ND_MOD)
          println("\tld.%c %c%d, %c0", suffix, reg, to_reg, reg);
        println("\tld.p p1, @sp+");
        indents--; return ret;
      case ND_BITAND:
        println("\tand.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        indents--; return ret;
      case ND_BITOR:
        println("\tor.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        indents--; return ret;
      case ND_BITXOR:
        println("\txor.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        indents--; return ret;
      case ND_EQ: {
        int c = count();
        println("\tcp.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tldq p%d, $01", to_reg);
        println("\tjr.s __L_eq_%d", c);
        println("__L_ne_%d:", c);
        println("\tldq p%d, $00", to_reg);
        println("__L_eq_%d:", c);
        indents--; return ret;
      }
      case ND_NE: {
        int c = count();
        println("\tcp.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        println("\tjr ne, __L_ne_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_eq_%d", c);
        println("__L_ne_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_eq_%d:", c);
        indents--; return ret;
      }
      case ND_LT: {
        int c = count();
        println("\tcp.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        if (node->lhs->ty->is_unsigned)
          println("\tjr ult, __L_lt_%d", c);
        else
          println("\tjr lt, __L_lt_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_ge_%d", c);
        println("__L_lt_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_ge_%d:", c);
        indents--; return ret;
      }
      case ND_LE: {
        int c = count();
        println("\tcp.%c %c%d, %c%d", suffix, reg, to_reg, reg, rec_reg);
        if (node->lhs->ty->is_unsigned)
          println("\tjr ule, __L_le_%d", c);
        else
          println("\tjr le, __L_le_%d", c);
        println("\tldq p%d, $00", to_reg);
        println("\tjr.s __L_gt_%d", c);
        println("__L_le_%d:", c);
        println("\tldq p%d, $01", to_reg);
        println("__L_gt_%d:", c);
        indents--; return ret;
      }
      case ND_SHL: {
        int c = count();
        println("__L_shl_%d:", c);
        println("\tcp.%c %c%d, 0", suffix, reg, rec_reg);
        println("\tjr le, __L_shlbreak_%d", c);
        println("\tsbq.%c %c%d, 1", suffix, reg, rec_reg);
        println("\tsla.%c %c%d", suffix, reg, to_reg);
        println("\tjr.s __L_shl_%d", c);
        println("__L_shlbreak_%d:", c);
        indents--; return ret;
      }
      case ND_SHR:{
        int c = count();
        println("__L_shr_%d:", c);
        println("\tcp.%c %c%d, 0", suffix, reg, rec_reg);
        println("\tjr le, __L_shrbreak_%d", c);
        println("\tsbq.%c %c%d, 1", suffix, reg, rec_reg);
        if (node->lhs->ty->is_unsigned)
          println("\tsra.%c %c%d", suffix, reg, to_reg);
        else
          println("\tsrl.%c %c%d", suffix, reg, to_reg);
        println("\tjr.s __L_shr_%d", c);
        println("__L_shrbreak_%d:", c);
        indents--; return ret;
      }
      default:
        error_tok(node->tok, "invalid expression");
        break;
    }
  }
}

static void gen_stmt(Node *node) {
  //println("\t; .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  switch (node->kind) {
    case ND_IF: {
      int c = count();
      gen_expr(node->cond, true, false);
      cmp_zero(node->cond->ty, get_reg_type(node->cond->ty));
      println("\tjr nz, __L_then_%d", c);
      println("\tjr.l __L_else_%d", c);
      println("__L_then_%d:", c);
      gen_stmt(node->then);
      println("\tjr.l __L_end_%d", c);
      println("__L_else_%d:", c);
      if (node->els)
        gen_stmt(node->els);
      println("__L_end_%d:", c);
      return;
    }
    case ND_FOR: {
      int c = count();
      if (node->init)
        gen_stmt(node->init);
      println("__L_begin_%d:", c);
      if (node->cond) {
        gen_expr(node->cond, true, false);
        cmp_zero(node->cond->ty, get_reg_type(node->cond->ty));
        println("\tjr nz, __L_continue_%d", c);
        println("\tjr.l %s", node->brk_label);
        println("__L_continue_%d:", c);
      }
      gen_stmt(node->then);
      println("%s:", node->cont_label);
      if (node->inc)
        gen_expr(node->inc, true, false);
      println("\tjr.l __L_begin_%d", c);
      println("%s:", node->brk_label);
      return;
    }
    case ND_DO: {
      int c = count();
      println("__L_begin_%d:", c);
      gen_stmt(node->then);
      println("%s:", node->cont_label);
      gen_expr(node->cond, true, false);
      cmp_zero(node->cond->ty, get_reg_type(node->cond->ty));
      println("\tjr z, %s", node->brk_label);
      println("\tjr.l __L_begin_%d", c);
      println("%s:", node->brk_label);
      return;
    }
    case ND_SWITCH:
      gen_expr(node->cond, true, false);
      
      for (Node *n = node->case_next; n; n = n->case_next) {
        char suffix = get_suffix(node->cond->ty->size);
        char reg = get_stack_reg(node->cond->ty->size);
        
        int c = count();
        int to_reg;
        if (node->cond->ty->size == 4)
          to_reg = to_lp_reg;
        else
          to_reg = to_gp_reg;
        
        if (n->begin == n->end) {
          if (node->cond->ty->size == 4) {
            println("\tcp.w @__long_%d0, %hu", to_reg, (uint16_t)(n->begin & 0xffff));
            println("\tjr ne, __L_ne_%d", c);
            println("\tcp.w @__long_%d1, %hu", to_reg, (uint16_t)(n->begin >> 16));
            println("\tjr ne, __L_ne_%d", c);
            println("\tjr.l %s", n->label);
            println("__L_ne_%d:", c);
          }
          else {
            println("\tcp.%c %c%d, %d", suffix, reg, to_reg, (int32_t)(n->begin));
            println("\tjr ne, __L_ne_%d", c);
            println("\tjr.l %s", n->label);
            println("__L_ne_%d:", c);
          }
          continue;
        }
      
        // [GNU] Case ranges
        if (node->cond->ty->size == 4) {
          println("\tld.w @__long_20, @__long_%d0", to_reg);
          println("\tld.w @__long_21, @__long_%d1", to_reg);
          println("\tsub.w @__long_20, %hu", (uint16_t)(n->begin & 0xffff));
          println("\tsbx.w @__long_21, %hu", (uint16_t)(n->begin >> 16));
          println("\tcp.w @__long_21, %hu", (uint16_t)((n->end - n->begin) >> 16));
          println("\tjr ugt, __L_gt_%d", c);
          println("\tcp.w @__long_20, %hu", (uint16_t)((n->end - n->begin) & 0xffff));
          println("\tjr ugt, __L_gt_%d", c);
          println("\tjr.l %s", n->label);
          println("__L_gt_%d:", c);
        }
        else {
          println("\tld.%c %c0, %c%d", suffix, reg, reg, to_reg);
          if (n->begin <= 8)
            println("\tsbq.%c %c0, %d", suffix, reg, (int32_t)(n->begin));
          else
            println("\tsub.%c %c0, %d", suffix, reg, (int32_t)(n->begin));
          println("\tcp.%c %c0, %d", suffix, reg, (int32_t)(n->end - n->begin));
          println("\tjr ugt, __L_gt_%d", c);
          println("\tjr.l %s", n->label);
          println("__L_gt_%d:", c);
        }
      }

      if (node->default_case)
        println("\tjr.l %s", node->default_case->label);

      println("\tjr.l %s", node->brk_label);
      gen_stmt(node->then);
      println("%s:", node->brk_label);
      return;
    case ND_CASE:
      println("%s:", node->label);
      gen_stmt(node->lhs);
      return;
    case ND_BLOCK:
      for (Node *n = node->body; n; n = n->next)
        gen_stmt(n);
      return;
    case ND_GOTO:
      println("\tjr.l %s", node->unique_label);
      return;
    case ND_GOTO_EXPR:
      gen_expr(node->lhs, true, false);
      println("\tjr.l p%d", to_gp_reg);
      return;
    case ND_LABEL:
      println("%s:", node->unique_label);
      gen_stmt(node->lhs);
      return;
    case ND_RETURN:
      if (node->lhs) {
        Type *ty = node->lhs->ty;
        gen_expr(node->lhs, true, true);
        
        switch (ty->kind) {
          case TY_STRUCT:
          case TY_UNION:
            copy_struct(0);
          default:
            break;
        }
      }
      
      println("\tjr.l __L_return_%s", current_fn->name);
      return;
    case ND_EXPR_STMT:
      gen_expr(node->lhs, true, false);
      return;
    case ND_ASM:
      println("\t%s", node->asm_str);
      return;
    default:
      error_tok(node->tok, "invalid statement");
      return;
  }
}

// Assign offsets to local variables.
static void assign_lvar_offsets(Obj *prog) {
  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function)
      continue;
    
    // If a function has many parameters, some parameters are
    // inevitably passed by stack rather than by register.
    // The first passed-by-stack parameter resides at p6+4.
    int top = 4;
    int bottom = 0;
    
    int gp = 0, fp = 0, dp = 0;
    
    // Assign offsets to pass-by-stack parameters.
    for (Obj *var = fn->params; var; var = var->next) {
      Type *ty = var->ty;
      
      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        break;
      case TY_FLOAT:
        if (fp++ < FP_MAX)
          continue;
        break;
      case TY_DOUBLE:
        if (dp++ < DP_MAX)
          continue;
        break;
      default:
        if (gp++ < GP_MAX)
          continue;
      }

      top = align_to(top, var->align);
      var->offset = top;
      top += var->ty->size;
    }
    
    // Assign offsets to pass-by-register parameters and local variables.
    for (Obj *var = fn->locals; var; var = var->next) {
      if (var->offset)
        continue;
      
      bottom += var->ty->size;
      bottom = align_to(bottom, var->align);
      var->offset = -bottom;
    }
    
    fn->stack_size = align_to(bottom, 2);
  }
}

static void emit_data(Obj *prog) {
  println("__data_start:");
  bool dot_data = true;
  
  for (Obj *var = prog; var; var = var->next) {
    if (var->is_function || !var->is_definition)
      continue;
    
    /*
    if (var->is_static)
      println("\t; .local %s", var->name);
    else
      println("\t; .globl %s", var->name);
    
    // Common symbol (imported)
    if (opt_fcommon && var->is_tentative) {
      println("\t; .comm %s, %d, %d", var->name, var->ty->size, var->align);
      continue;
    }
    */
    
    // .data
    if (var->init_data) {
      //println("\t; .data");
      if (!dot_data) {
        println("#bank rom");
        dot_data = true;
      }
      /*
      println("\t; .type %s, @object", var->name);
      println("\t; .size %s, %d", var->name, var->ty->size);
      println("\t; .align %d", var->align);
      */
      println("#align %d", var->align << 3);
      println("%s:", var->name);
      
      Relocation *rel = var->rel;
      int pos = 0;
      while (pos < var->ty->size) {
        if (rel && rel->offset == pos) {
          println("#d32 %s%+ld", *rel->label, rel->addend);
          rel = rel->next;
          pos += 4;
        } else {
          println("#d8 %d", var->init_data[pos++]);
        }
      }
      println("");
      continue;
    }
    
    // .bss
    else {
      //println("\t; .bss");
      if (dot_data) {
        println("#bank bss");
        dot_data = false;
      }
    }
    
    println("#align %d", var->align << 3);
    println("%s:", var->name);
    println("#res %d\n", var->ty->size);
  }
}

static void store_fp(int from_reg, int offset, int sz) {
  switch (sz) {
    case 4:
      println("\tld.w @p6+%d, @__float_%d0", offset, from_reg);
      println("\tld.w @p6+%d, @__float_%d1", offset + 2, from_reg);
      return;
    case 8:
      println("\tld.w @p6+%d, @__double_%d0", offset, from_reg);
      println("\tld.w @p6+%d, @__double_%d1", offset + 2, from_reg);
      println("\tld.w @p6+%d, @__double_%d2", offset + 4, from_reg);
      println("\tld.w @p6+%d, @__double_%d3", offset + 6, from_reg);
      return;
  }
  unreachable();
}

static void store_gp(int from_reg, int offset, int sz) {
  switch (sz) {
    case 1:
      println("\tld.b @p6+%d, l%d", offset, from_reg);
      return;
    case 2:
      println("\tld.w @p6+%d, w%d", offset, from_reg);
      return;
    case 3:
      println("\tld.p @p6+%d, p%d", offset, from_reg);
      return;
    case 4:
      println("\tld.w @p6+%d, @__long_%d0", offset, from_reg);
      println("\tld.w @p6+%d, @__long_%d1", offset + 2, from_reg);
      return;
  }
  unreachable();
}

static void emit_text(Obj *prog) {
  //println("\t; .text");
  println("#bank rom");
  println("__data_end:");
  
  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function || !fn->is_definition)
      continue;
    
    // No code is emitted for "static inline" functions
    // if no one is referencing them.
    if (!fn->is_live)
      continue;
    
    println("\t; %s:%d", fn->body->tok->file->name, fn->body->tok->line_no);
    
    /*
    if (fn->is_static)
      println("\t; .local %s", fn->name);
    else
      println("\t; .globl %s", fn->name);
    */
    
    //println("\t; .type %s, @function", fn->name);
    println("%s:", fn->name);
    current_fn = fn;
    
    // Prologue
    println("\tld.p @-sp, p6");
    println("\tld.p p6, sp");
    if (fn->stack_size <= 8)
      println("\tsbq.p sp, %d", fn->stack_size);
    else
      println("\tsub.p sp, %d", fn->stack_size);
    println("\tld.p @p6+%d, sp", fn->alloca_bottom->offset);
    
    // Save arg registers if function is variadic
    if (fn->va_area) {
      int gp = 0, fp = 0, dp = 0;
      for (Obj *var = fn->params; var; var = var->next) {
        if (var->ty->kind == TY_FLOAT)
          fp++;
        else if (var->ty->kind == TY_DOUBLE)
          dp++;
        else
          gp += var->align;
      }
      
      int off = fn->va_area->offset;
      
      // va_elem
      println("\tld.p @p6+%d, %d", off, gp);                // gp_offset
      println("\tld.p @p6+%d, %d", off + 4, fp * 4 + 20);   // fp_offset
      println("\tld.p @p6+%d, %d", off + 8, dp * 8 + 28);   // dp_offset
      println("\tld.p @p6+%d, p6", off + 12);               // overflow_arg_area
      println("\tadd.p @p6+%d, 4", off + 12);
      println("\tld.p @p6+%d, p6", off + 16);               // reg_save_area
      println("\tadd.p @p6+%d, %d", off + 16, off + 24);
      
      // __reg_save_area__
      println("\tld.p @p6+%d, p1", off + 24);
      println("\tld.p @p6+%d, p2", off + 28);
      println("\tld.p @p6+%d, p3", off + 32);
      println("\tld.w @p6+%d, @__long_01", off + 36);
      println("\tld.w @p6+%d, @__long_00", off + 38);
      println("\tld.w @p6+%d, @__long_11", off + 40);
      println("\tld.w @p6+%d, @__long_10", off + 42);
      println("\tld.w @p6+%d, @__float_01", off + 44);
      println("\tld.w @p6+%d, @__float_00", off + 46);
      println("\tld.w @p6+%d, @__float_11", off + 48);
      println("\tld.w @p6+%d, @__float_10", off + 50);
      println("\tld.w @p6+%d, @__double_03", off + 52);
      println("\tld.w @p6+%d, @__double_02", off + 54);
      println("\tld.w @p6+%d, @__double_01", off + 56);
      println("\tld.w @p6+%d, @__double_00", off + 58);
      println("\tld.w @p6+%d, @__double_13", off + 60);
      println("\tld.w @p6+%d, @__double_12", off + 62);
      println("\tld.w @p6+%d, @__double_11", off + 64);
      println("\tld.w @p6+%d, @__double_10", off + 66);
    }

    // Save passed-by-register arguments to the stack
    int gp = 0, fp = 0, dp = 0, lp = 0;
    for (Obj *var = fn->params; var; var = var->next) {
      if (var->offset > 0)
        continue;

      Type *ty = var->ty;
      
      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        store_gp(gp++, var->offset, 3);
        break;
      case TY_FLOAT:
        store_fp(fp++, var->offset, ty->size);
        break;
      case TY_DOUBLE:
        store_fp(dp++, var->offset, ty->size);
        break;
      case TY_LONG:
      case TY_ENUM:
        store_gp(lp++, var->offset, ty->size);
        break;
      default:
        store_gp(gp++, var->offset, ty->size);
      }
    }
    
    to_gp_reg = GP_SCRATCH_START;
    to_fp_reg = 0;
    to_dp_reg = 0;
    to_lp_reg = 0;
    
    // Emit code
    gen_stmt(fn->body);
    assert(depth == 0);
    
    // [https://www.sigbus.info/n1570#5.1.2.2.3p1] The C spec defines
    // a special rule for the main function. Reaching the end of the
    // main function is equivalent to returning 0, even though the
    // behavior is undefined for the other functions.
    if (strcmp(fn->name, "main") == 0)
      println("\tldq p0, $00");
    
    // Epilogue
    println("__L_return_%s:", fn->name);
    println("\tld.p sp, p6");
    println("\tld.p p6, @sp+");
    println("\tjp @sp+");
  }
}

void codegen(Obj *prog, FILE *out) {
  output_file = out;
  
  assign_lvar_offsets(prog);
  emit_data(prog);
  emit_text(prog);
}
