#include<inttypes.h>
#include<stdbool.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

#include"sail.h"

/*
 * Temporary mpzs for use in functions below. To avoid conflicts, only
 * use in functions that do not call other functions in this file.
 */
static sail_int sail_lib_tmp1, sail_lib_tmp2;

#define FLOAT_PRECISION 255

void setup_library(void)
{
  mpz_init(sail_lib_tmp1);
  mpz_init(sail_lib_tmp2);
  mpf_set_default_prec(FLOAT_PRECISION);
}

void cleanup_library(void)
{
  mpz_clear(sail_lib_tmp1);
  mpz_clear(sail_lib_tmp2);
}

bool eq_unit(const unit a, const unit b)
{
  return true;
}

unit UNDEFINED(unit)(const unit u)
{
  return UNIT;
}

/* ***** Sail bit type ***** */

bool eq_bit(const mach_bits a, const mach_bits b)
{
  return a == b;
}

/* ***** Sail booleans ***** */

bool not(const bool b) {
  return !b;
}

bool eq_bool(const bool a, const bool b) {
  return a == b;
}

bool UNDEFINED(bool)(const unit u) {
  return false;
}

/* ***** Sail strings ***** */

void CREATE(sail_string)(sail_string *str)
{
  char *istr = (char *) malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void RECREATE(sail_string)(sail_string *str)
{
  free(*str);
  char *istr = (char *) malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void COPY(sail_string)(sail_string *str1, const sail_string str2)
{
  size_t len = strlen(str2);
  *str1 = realloc(*str1, len + 1);
  *str1 = strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str)
{
  free(*str);
}

void dec_str(sail_string *str, const mpz_t n)
{
  free(*str);
  gmp_asprintf(str, "%Zd", n);
}

void hex_str(sail_string *str, const mpz_t n)
{
  free(*str);
  gmp_asprintf(str, "0x%Zx", n);
}

bool eq_string(const sail_string str1, const sail_string str2)
{
  return strcmp(str1, str2) == 0;
}

void undefined_string(sail_string *str, const unit u) {}

void concat_str(sail_string *stro, const sail_string str1, const sail_string str2)
{
  *stro = realloc(*stro, strlen(str1) + strlen(str2) + 1);
  (*stro)[0] = '\0';
  strcat(*stro, str1);
  strcat(*stro, str2);
}

/* ***** Sail integers ***** */

#ifndef USE_INT128

inline
void COPY(sail_int)(sail_int *rop, const sail_int op)
{
  mpz_set(*rop, op);
}

inline
void CREATE(sail_int)(sail_int *rop)
{
  mpz_init(*rop);
}

inline
void RECREATE(sail_int)(sail_int *rop)
{
  mpz_set_ui(*rop, 0);
}

inline
void KILL(sail_int)(sail_int *rop)
{
  mpz_clear(*rop);
}

inline
void CREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_init_set_si(*rop, op);
}

inline
void RECREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_set_si(*rop, op);
}

inline
void CREATE_OF(sail_int, sail_string)(sail_int *rop, sail_string str)
{
  mpz_init_set_str(*rop, str, 10);
}

inline
void RECREATE_OF(sail_int, sail_string)(mpz_t *rop, sail_string str)
{
  mpz_set_str(*rop, str, 10);
}

inline
mach_int CONVERT_OF(mach_int, sail_int)(const sail_int op)
{
  return mpz_get_si(op);
}

inline
void CONVERT_OF(sail_int, mach_int)(sail_int *rop, const mach_int op)
{
  mpz_set_si(*rop, op);
}

inline
bool eq_int(const sail_int op1, const sail_int op2)
{
  return !abs(mpz_cmp(op1, op2));
}

inline
bool lt(const sail_int op1, const sail_int op2)
{
  return mpz_cmp(op1, op2) < 0;
}

inline
bool gt(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) > 0;
}

inline
bool lteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) <= 0;
}

inline
bool gteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) >= 0;
}

inline
void shl_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul_2exp(*rop, op1, mpz_get_ui(op2));
}

inline
void shr_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q_2exp(*rop, op1, mpz_get_ui(op2));
}

inline
void undefined_int(sail_int *rop, const int n)
{
  mpz_set_ui(*rop, (uint64_t) n);
}

inline
void undefined_range(sail_int *rop, const sail_int l, const sail_int u)
{
  mpz_set(*rop, l);
}

inline
void add_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_add(*rop, op1, op2);
}

inline
void sub_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_sub(*rop, op1, op2);
}

inline
void mult_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul(*rop, op1, op2);
}

inline
void tdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_q(*rop, op1, op2);
}

inline
void tmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_r(*rop, op1, op2);
}

inline
void fdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q(*rop, op1, op2);
}

inline
void fmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_r(*rop, op1, op2);
}

void max_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (lt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void min_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (gt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

inline
void neg_int(sail_int *rop, const sail_int op)
{
  mpz_neg(*rop, op);
}

inline
void abs_int(sail_int *rop, const sail_int op)
{
  mpz_abs(*rop, op);
}

void pow2(sail_int *rop, const sail_int exp) {
  /* Assume exponent is never more than 2^64... */
  uint64_t exp_ui = mpz_get_ui(exp);
  mpz_t base;
  mpz_init_set_ui(base, 2ul);
  mpz_pow_ui(*rop, base, exp_ui);
  mpz_clear(base);
}

#endif

/* ***** Sail bitvectors ***** */

void CREATE(sail_bits)(sail_bits *rop)
{
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = 0;
  mpz_init(*rop->bits);
}

void RECREATE(sail_bits)(sail_bits *rop)
{
  rop->len = 0;
  mpz_set_ui(*rop->bits, 0);
}

void COPY(sail_bits)(sail_bits *rop, const sail_bits op)
{
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
}

void KILL(sail_bits)(sail_bits *rop)
{
  mpz_clear(*rop->bits);
  free(rop->bits);
}

void CREATE_OF(sail_bits, mach_bits)(sail_bits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->bits = malloc(sizeof(mpz_t));
  rop->len = len;
  mpz_init_set_ui(*rop->bits, op);
}

void RECREATE_OF(sail_bits, mach_bits)(sail_bits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->len = len;
  mpz_set_ui(*rop->bits, op);
}

mach_bits CONVERT_OF(mach_bits, sail_bits)(const sail_bits op)
{
  return mpz_get_ui(*op.bits);
}

void CONVERT_OF(sail_bits, mach_bits)(sail_bits *rop, const mach_bits op, const uint64_t len)
{
  rop->len = len;
  // use safe_rshift to correctly handle the case when we have a 0-length vector.
  mpz_set_ui(*rop->bits, op & safe_rshift(UINT64_MAX, 64 - len));
}

void UNDEFINED(sail_bits)(sail_bits *rop, const sail_int len, const mach_bits bit)
{
  zeros(rop, len);
}

mach_bits UNDEFINED(mach_bits)(const unit u) { return 0; }

mach_bits safe_rshift(const mach_bits x, const mach_bits n)
{
  if (n >= 64) {
    return 0ul;
  } else {
    return x >> n;
  }
}

void normalize_sail_bits(sail_bits *rop) {
  /* TODO optimisation: keep a set of masks of various sizes handy */
  mpz_set_ui(sail_lib_tmp1, 1);
  mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, rop->len);
  mpz_sub_ui(sail_lib_tmp1, sail_lib_tmp1, 1);
  mpz_and(*rop->bits, *rop->bits, sail_lib_tmp1);
}

void append_64(sail_bits *rop, const sail_bits op, const mach_bits chunk)
{
  rop->len = rop->len + 64ul;
  mpz_mul_2exp(*rop->bits, *op.bits, 64ul);
  mpz_add_ui(*rop->bits, *rop->bits, chunk);
}

void add_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
  normalize_sail_bits(rop);
}

void sub_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, *op2.bits);
  normalize_sail_bits(rop);
}

void add_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
  normalize_sail_bits(rop);
}

void sub_bits_int(sail_bits *rop, const sail_bits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, op2);
  normalize_sail_bits(rop);
}

void and_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_and(*rop->bits, *op1.bits, *op2.bits);
}

void or_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_ior(*rop->bits, *op1.bits, *op2.bits);
}

void xor_bits(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len;
  mpz_xor(*rop->bits, *op1.bits, *op2.bits);
}

void not_bits(sail_bits *rop, const sail_bits op)
{
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
  for (mp_bitcnt_t i = 0; i < op.len; i++) {
    mpz_combit(*rop->bits, i);
  }
}

void zeros(sail_bits *rop, const sail_int op)
{
  rop->len = mpz_get_ui(op);
  mpz_set_ui(*rop->bits, 0);
}

void zero_extend(sail_bits *rop, const sail_bits op, const sail_int len)
{
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
}

void length_sail_bits(sail_int *rop, const sail_bits op)
{
  mpz_set_ui(*rop, op.len);
}

bool eq_bits(const sail_bits op1, const sail_bits op2)
{
  for (mp_bitcnt_t i = 0; i < op1.len; i++) {
    if (mpz_tstbit(*op1.bits, i) != mpz_tstbit(*op2.bits, i)) return false;
  }
  return true;
}

void vector_subrange_sail_bits(sail_bits *rop,
			       const sail_bits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  rop->len = n - (m - 1ul);
  mpz_fdiv_q_2exp(*rop->bits, *op.bits, m);
  normalize_sail_bits(rop);
}

void truncate(sail_bits *rop, const sail_bits op, const sail_int len)
{
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
  normalize_sail_bits(rop);
}

mach_bits bitvector_access(const sail_bits op, const sail_int n_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  return (mach_bits) mpz_tstbit(*op.bits, n);
}

void sail_unsigned(sail_int *rop, const sail_bits op)
{
  /* Normal form of bv_t is always positive so just return the bits. */
  mpz_set(*rop, *op.bits);
}

void sail_signed(sail_int *rop, const sail_bits op)
{
  if (op.len == 0) {
    mpz_set_ui(*rop, 0);
  } else {
    mp_bitcnt_t sign_bit = op.len - 1;
    mpz_set(*rop, *op.bits);
    if (mpz_tstbit(*op.bits, sign_bit) != 0) {
      /* If sign bit is unset then we are done,
         otherwise clear sign_bit and subtract 2**sign_bit */
      mpz_set_ui(sail_lib_tmp1, 1);
      mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, sign_bit); /* 2**sign_bit */
      mpz_combit(*rop, sign_bit); /* clear sign_bit */
      mpz_sub(*rop, *rop, sail_lib_tmp1);
    }
  }
}

void append(sail_bits *rop, const sail_bits op1, const sail_bits op2)
{
  rop->len = op1.len + op2.len;
  mpz_mul_2exp(*rop->bits, *op1.bits, op2.len);
  mpz_ior(*rop->bits, *rop->bits, *op2.bits);
}

void replicate_bits(sail_bits *rop, const sail_bits op1, const mpz_t op2)
{
  uint64_t op2_ui = mpz_get_ui(op2);
  rop->len = op1.len * op2_ui;
  mpz_set(*rop->bits, *op1.bits);
  for (int i = 1; i < op2_ui; i++) {
    mpz_mul_2exp(*rop->bits, *rop->bits, op1.len);
    mpz_ior(*rop->bits, *rop->bits, *op1.bits);
  }
}

uint64_t fast_replicate_bits(const uint64_t shift, const uint64_t v, const int64_t times)
{
  uint64_t r = v;
  for (int i = 1; i < times; ++i) {
    r |= (r << shift);
  }
  return r;
}

// Takes a slice of the (two's complement) binary representation of
// integer n, starting at bit start, and of length len. With the
// argument in the following order:
//
// get_slice_int(len, n, start)
//
// For example:
//
// get_slice_int(8, 1680, 4) =
//
//                    11           0
//                    V            V
// get_slice_int(8, 0b0110_1001_0000, 4) = 0b0110_1001
//                    <-------^
//                    (8 bit) 4
//
void get_slice_int(sail_bits *rop, const sail_int len_mpz, const sail_int n, const sail_int start_mpz)
{
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(n, i + start)) mpz_setbit(*rop->bits, i);
  }
}

// Set slice uses the same indexing scheme as get_slice_int, but it
// puts a bitvector slice into an integer rather than returning it.
void set_slice_int(sail_int *rop,
		   const sail_int len_mpz,
		   const sail_int n,
		   const sail_int start_mpz,
		   const sail_bits slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop, n);

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop, i + start);
    } else {
      mpz_clrbit(*rop, i + start);
    }
  }
}

void vector_update_subrange_sail_bits(sail_bits *rop,
				 const sail_bits op,
				 const sail_int n_mpz,
				 const sail_int m_mpz,
				 const sail_bits slice)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  mpz_set(*rop->bits, *op.bits);

  for (uint64_t i = 0; i < n - (m - 1ul); i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + m);
    } else {
      mpz_clrbit(*rop->bits, i + m);
    }
  }
}

void slice(sail_bits *rop, const sail_bits op, const sail_int start_mpz, const sail_int len_mpz)
{
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(*op.bits, i + start)) mpz_setbit(*rop->bits, i);
  }
}

void set_slice(sail_bits *rop,
	       const sail_int len_mpz,
	       const sail_int slen_mpz,
	       const sail_bits op,
	       const sail_int start_mpz,
	       const sail_bits slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + start);
    } else {
      mpz_clrbit(*rop->bits, i + start);
    }
  }
}

/* ***** Sail Reals ***** */

void CREATE(real)(real *rop)
{
  mpf_init(*rop);
}

void RECREATE(real)(real *rop)
{
  mpf_set_ui(*rop, 0);
}

void KILL(real)(real *rop)
{
  mpf_clear(*rop);
}

void COPY(real)(real *rop, const real op)
{
  mpf_set(*rop, op);
}

void UNDEFINED(real)(real *rop, unit u)
{
  mpf_set_ui(*rop, 0ul);
}

void neg_real(real *rop, const real op)
{
  mpf_neg(*rop, op);
}

void mult_real(real *rop, const real op1, const real op2) {
  mpf_mul(*rop, op1, op2);
}

void sub_real(real *rop, const real op1, const real op2)
{
  mpf_sub(*rop, op1, op2);
}

void add_real(real *rop, const real op1, const real op2)
{
  mpf_add(*rop, op1, op2);
}

void div_real(real *rop, const real op1, const real op2)
{
  mpf_div(*rop, op1, op2);
}

void sqrt_real(real *rop, const real op)
{
  mpf_sqrt(*rop, op);
}

void abs_real(real *rop, const real op)
{
  mpf_abs(*rop, op);
}

void round_up(sail_int *rop, const real op)
{
  mpf_t x;
  mpf_init(x);
  mpf_ceil(x, op);
  mpz_set_ui(*rop, mpf_get_ui(x));
  mpf_clear(x);
}

void round_down(sail_int *rop, const real op)
{
  mpf_t x;
  mpf_init(x);
  mpf_floor(x, op);
  mpz_set_ui(*rop, mpf_get_ui(x));
  mpf_clear(x);
}

void to_real(real *rop, const sail_int op)
{
  mpf_set_z(*rop, op);
}

bool eq_real(const real op1, const real op2)
{
  return mpf_cmp(op1, op2) == 0;
}

bool lt_real(const real op1, const real op2)
{
  return mpf_cmp(op1, op2) < 0;
}

bool gt_real(const real op1, const real op2)
{
  return mpf_cmp(op1, op2) > 0;
}

bool lteq_real(const real op1, const real op2)
{
  return mpf_cmp(op1, op2) <= 0;
}

bool gteq_real(const real op1, const real op2)
{
  return mpf_cmp(op1, op2) >= 0;
}

void real_power(real *rop, const real base, const sail_int exp)
{
  uint64_t exp_ui = mpz_get_ui(exp);
  mpf_pow_ui(*rop, base, exp_ui);
}

void CREATE_OF(real, sail_string)(real *rop, const sail_string op)
{
  mpf_init(*rop);
  gmp_sscanf(op, "%Ff", *rop);
}

/* ***** Printing functions ***** */

void string_of_int(sail_string *str, const sail_int i)
{
  gmp_asprintf(str, "%Zd", i);
}

void string_of_bits(sail_string *str, const sail_bits op)
{
  if ((op.len % 4) == 0) {
    gmp_asprintf(str, "0x%*0Zx", op.len / 4, *op.bits);
  } else {
    gmp_asprintf(str, "0b%*0Zb", op.len, *op.bits);
  }
}

void fprint_bits(const sail_string pre,
		 const sail_bits op,
		 const sail_string post,
		 FILE *stream)
{
  fputs(pre, stream);

  if (op.len % 4 == 0) {
    fputs("0x", stream);
    mpz_t buf;
    mpz_init_set(buf, *op.bits);

    char *hex = malloc((op.len / 4) * sizeof(char));

    for (int i = 0; i < op.len / 4; ++i) {
      char c = (char) ((0xF & mpz_get_ui(buf)) + 0x30);
      hex[i] = (c < 0x3A) ? c : c + 0x7;
      mpz_fdiv_q_2exp(buf, buf, 4);
    }

    for (int i = op.len / 4; i > 0; --i) {
      fputc(hex[i - 1], stream);
    }

    free(hex);
    mpz_clear(buf);
  } else {
    fputs("0b", stream);
    for (int i = op.len; i > 0; --i) {
      fputc(mpz_tstbit(*op.bits, i - 1) + 0x30, stream);
    }
  }

  fputs(post, stream);
}

unit print_bits(const sail_string str, const sail_bits op)
{
  fprint_bits(str, op, "\n", stdout);
  return UNIT;
}

unit prerr_bits(const sail_string str, const sail_bits op)
{
  fprint_bits(str, op, "\n", stderr);
  return UNIT;
}

unit print(const sail_string str)
{
  printf("%s", str);
  return UNIT;
}

unit print_endline(const sail_string str)
{
  printf("%s\n", str);
  return UNIT;
}

unit prerr(const sail_string str)
{
  fprintf(stderr, "%s", str);
  return UNIT;
}

unit prerr_endline(const sail_string str)
{
  fprintf(stderr, "%s\n", str);
  return UNIT;
}

unit print_int(const sail_string str, const sail_int op)
{
  fputs(str, stdout);
  mpz_out_str(stdout, 10, op);
  putchar('\n');
  return UNIT;
}

unit prerr_int(const sail_string str, const sail_int op)
{
  fputs(str, stderr);
  mpz_out_str(stderr, 10, op);
  fputs("\n", stderr);
  return UNIT;
}

unit sail_putchar(const sail_int op)
{
  char c = (char) mpz_get_ui(op);
  putchar(c);
  return UNIT;
}
