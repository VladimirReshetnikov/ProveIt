#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>
#include <omp.h>

#if defined(__has_include)
#  if __has_include(<mpfr.h>)
#    include <mpfr.h>
#    define HAVE_SYSTEM_MPFR_HEADER 1
#  endif
#endif

#ifndef HAVE_SYSTEM_MPFR_HEADER
/* Minimal declarations for the MPFR 4.x ABI.  The execution environment had
   libmpfr.so.6 but not the development header package.  A normal build with
   libmpfr-dev installed takes the branch above instead. */
typedef unsigned long mp_limb_t;
typedef long mpfr_prec_t;
typedef long mpfr_exp_t;
typedef int mpfr_sign_t;
typedef struct {
  mpfr_prec_t _mpfr_prec;
  mpfr_sign_t _mpfr_sign;
  mpfr_exp_t _mpfr_exp;
  mp_limb_t *_mpfr_d;
} __mpfr_struct;
typedef __mpfr_struct mpfr_t[1];
typedef __mpfr_struct *mpfr_ptr;
typedef const __mpfr_struct *mpfr_srcptr;
typedef enum {
  MPFR_RNDN = 0, MPFR_RNDZ = 1, MPFR_RNDU = 2,
  MPFR_RNDD = 3, MPFR_RNDA = 4, MPFR_RNDF = 5,
  MPFR_RNDNA = -1
} mpfr_rnd_t;
extern void mpfr_init2(mpfr_ptr, mpfr_prec_t);
extern void mpfr_clear(mpfr_ptr);
extern int mpfr_set_ui(mpfr_ptr, unsigned long, mpfr_rnd_t);
extern int mpfr_log(mpfr_ptr, mpfr_srcptr, mpfr_rnd_t);
extern int mpfr_mul(mpfr_ptr, mpfr_srcptr, mpfr_srcptr, mpfr_rnd_t);
extern int mpfr_sub(mpfr_ptr, mpfr_srcptr, mpfr_srcptr, mpfr_rnd_t);
extern int mpfr_cmp_ui(mpfr_srcptr, unsigned long);
extern double mpfr_get_d(mpfr_srcptr, mpfr_rnd_t);
extern const char *mpfr_get_version(void);
#endif

static inline int is_power_of_two_u64(uint64_t x) {
  return x && ((x & (x - 1)) == 0);
}

typedef struct {
  uint64_t checked;
  uint64_t failures;
  double min_lower;
  double min_upper;
  uint64_t min_lower_m, min_lower_n;
  uint64_t min_upper_m, min_upper_n;
  uint64_t first_fail_m, first_fail_guess;
} Stats;

int main(int argc, char **argv) {
  uint64_t start = 1;
  uint64_t limit = (1ULL << 20);
  int bits = 192;
  if (argc > 1) start = strtoull(argv[1], NULL, 0);
  if (argc > 2) limit = strtoull(argv[2], NULL, 0);
  if (argc > 3) bits = atoi(argv[3]);
  if (start < 1 || limit <= start) {
    fprintf(stderr, "bad range\n");
    return 2;
  }

  int nt = omp_get_max_threads();
  Stats *stats = calloc((size_t)nt, sizeof(Stats));
  if (!stats) return 3;
  for (int i = 0; i < nt; ++i) {
    stats[i].min_lower = INFINITY;
    stats[i].min_upper = INFINITY;
  }

  const long double theta = logl(3.0L) / logl(2.0L);
  double t0 = omp_get_wtime();

  mpfr_t two, three, ln2_lo, ln2_hi, ln3_lo, ln3_hi;
  mpfr_init2(two, bits); mpfr_init2(three, bits);
  mpfr_init2(ln2_lo, bits); mpfr_init2(ln2_hi, bits);
  mpfr_init2(ln3_lo, bits); mpfr_init2(ln3_hi, bits);
  mpfr_set_ui(two, 2, MPFR_RNDN);
  mpfr_set_ui(three, 3, MPFR_RNDN);
  mpfr_log(ln2_lo, two, MPFR_RNDD);
  mpfr_log(ln2_hi, two, MPFR_RNDU);
  mpfr_log(ln3_lo, three, MPFR_RNDD);
  mpfr_log(ln3_hi, three, MPFR_RNDU);

#pragma omp parallel
  {
    int tid = omp_get_thread_num();
    Stats *st = &stats[tid];
    mpfr_t xm, xn, xnp1;
    mpfr_t logm_lo, logm_hi, logn_hi, lognp1_lo;
    mpfr_t lhs_lo, lhs_hi, rhs_lo, rhs_hi, dl, du;
    mpfr_init2(xm, bits); mpfr_init2(xn, bits); mpfr_init2(xnp1, bits);
    mpfr_init2(logm_lo, bits); mpfr_init2(logm_hi, bits);
    mpfr_init2(logn_hi, bits); mpfr_init2(lognp1_lo, bits);
    mpfr_init2(lhs_lo, bits); mpfr_init2(lhs_hi, bits);
    mpfr_init2(rhs_lo, bits); mpfr_init2(rhs_hi, bits);
    mpfr_init2(dl, bits); mpfr_init2(du, bits);

#pragma omp for schedule(static)
    for (uint64_t m = start; m < limit; ++m) {
      if (is_power_of_two_u64(m)) continue;

      /* This is only a locator.  The MPFR inequalities below are the proof. */
      uint64_t guess = (uint64_t)floorl(expl(theta * logl((long double)m)));

      mpfr_set_ui(xm, (unsigned long)m, MPFR_RNDN);
      mpfr_log(logm_lo, xm, MPFR_RNDD);
      mpfr_log(logm_hi, xm, MPFR_RNDU);
      mpfr_mul(lhs_lo, logm_lo, ln3_lo, MPFR_RNDD);
      mpfr_mul(lhs_hi, logm_hi, ln3_hi, MPFR_RNDU);

      int ok = 0;
      uint64_t certn = 0;
      double dl_d = 0.0, du_d = 0.0;
      static const int offsets[7] = {0, -1, 1, -2, 2, -3, 3};
      for (int oi = 0; oi < 7; ++oi) {
        int off = offsets[oi];
        if (off < 0 && guess < (uint64_t)(-off) + 1) continue;
        uint64_t n = (uint64_t)((int64_t)guess + off);
        if (n < 1) continue;

        mpfr_set_ui(xn, (unsigned long)n, MPFR_RNDN);
        mpfr_set_ui(xnp1, (unsigned long)(n + 1), MPFR_RNDN);

        /* Directed lower bound for log(m)log(3)-log(n)log(2). */
        mpfr_log(logn_hi, xn, MPFR_RNDU);
        mpfr_mul(rhs_hi, logn_hi, ln2_hi, MPFR_RNDU);
        mpfr_sub(dl, lhs_lo, rhs_hi, MPFR_RNDD);
        if (mpfr_cmp_ui(dl, 0) <= 0) continue;

        /* Directed lower bound for log(n+1)log(2)-log(m)log(3). */
        mpfr_log(lognp1_lo, xnp1, MPFR_RNDD);
        mpfr_mul(rhs_lo, lognp1_lo, ln2_lo, MPFR_RNDD);
        mpfr_sub(du, rhs_lo, lhs_hi, MPFR_RNDD);
        if (mpfr_cmp_ui(du, 0) <= 0) continue;

        ok = 1;
        certn = n;
        dl_d = mpfr_get_d(dl, MPFR_RNDD);
        du_d = mpfr_get_d(du, MPFR_RNDD);
        break;
      }

      if (!ok) {
        ++st->failures;
        if (!st->first_fail_m || m < st->first_fail_m) {
          st->first_fail_m = m;
          st->first_fail_guess = guess;
        }
        continue;
      }

      ++st->checked;
      if (dl_d < st->min_lower) {
        st->min_lower = dl_d;
        st->min_lower_m = m;
        st->min_lower_n = certn;
      }
      if (du_d < st->min_upper) {
        st->min_upper = du_d;
        st->min_upper_m = m;
        st->min_upper_n = certn;
      }
    }

    mpfr_clear(xm); mpfr_clear(xn); mpfr_clear(xnp1);
    mpfr_clear(logm_lo); mpfr_clear(logm_hi);
    mpfr_clear(logn_hi); mpfr_clear(lognp1_lo);
    mpfr_clear(lhs_lo); mpfr_clear(lhs_hi);
    mpfr_clear(rhs_lo); mpfr_clear(rhs_hi);
    mpfr_clear(dl); mpfr_clear(du);
  }

  Stats total = {0};
  total.min_lower = INFINITY;
  total.min_upper = INFINITY;
  for (int i = 0; i < nt; ++i) {
    Stats *s = &stats[i];
    total.checked += s->checked;
    total.failures += s->failures;
    if (s->min_lower < total.min_lower) {
      total.min_lower = s->min_lower;
      total.min_lower_m = s->min_lower_m;
      total.min_lower_n = s->min_lower_n;
    }
    if (s->min_upper < total.min_upper) {
      total.min_upper = s->min_upper;
      total.min_upper_m = s->min_upper_m;
      total.min_upper_n = s->min_upper_n;
    }
    if (s->first_fail_m &&
        (!total.first_fail_m || s->first_fail_m < total.first_fail_m)) {
      total.first_fail_m = s->first_fail_m;
      total.first_fail_guess = s->first_fail_guess;
    }
  }

  double elapsed = omp_get_wtime() - t0;
  printf("mpfr_version=%s\n", mpfr_get_version());
  printf("range=[%" PRIu64 ",%" PRIu64 ")\n", start, limit);
  printf("precision_bits=%d\nthreads=%d\n", bits, nt);
  printf("checked_nonpowers=%" PRIu64 "\n", total.checked);
  printf("failures=%" PRIu64 "\n", total.failures);
  printf("min_lower_log_margin=%.17g at (m,n)=(%" PRIu64 ",%" PRIu64 ")\n",
         total.min_lower, total.min_lower_m, total.min_lower_n);
  printf("min_upper_log_margin=%.17g at (m,n)=(%" PRIu64 ",%" PRIu64 ")\n",
         total.min_upper, total.min_upper_m, total.min_upper_n);
  if (total.failures) {
    printf("first_failure=(m,guess)=(%" PRIu64 ",%" PRIu64 ")\n",
           total.first_fail_m, total.first_fail_guess);
  }
  printf("elapsed_seconds=%.6f\n", elapsed);

  mpfr_clear(two); mpfr_clear(three);
  mpfr_clear(ln2_lo); mpfr_clear(ln2_hi);
  mpfr_clear(ln3_lo); mpfr_clear(ln3_hi);
  free(stats);
  return total.failures ? 1 : 0;
}
