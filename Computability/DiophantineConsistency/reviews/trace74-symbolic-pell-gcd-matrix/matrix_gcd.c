/* Independent companion-matrix computation of gcd(y_r(z), 2^(2B)-1).
 * No full Pell ordinate or graph-zero claim. See README for exact scope. */
#include <gmp.h>
#include <stdio.h>
#include <string.h>

typedef struct { mpz_t e[4]; } matrix;

static void matrix_init(matrix *m) {
  for (int i = 0; i < 4; ++i) mpz_init(m->e[i]);
}

static void matrix_clear(matrix *m) {
  for (int i = 0; i < 4; ++i) mpz_clear(m->e[i]);
}

static void matrix_swap(matrix *a, matrix *b) {
  for (int i = 0; i < 4; ++i) mpz_swap(a->e[i], b->e[i]);
}

/* `out` must be distinct from both operands. */
static void matrix_mul(matrix *out, const matrix *a, const matrix *b,
                       const mpz_t modulus, mpz_t t, mpz_t u) {
  for (int row = 0; row < 2; ++row) {
    for (int col = 0; col < 2; ++col) {
      mpz_mul(t, a->e[2 * row], b->e[col]);
      mpz_mul(u, a->e[2 * row + 1], b->e[2 + col]);
      mpz_add(t, t, u);
      mpz_mod(out->e[2 * row + col], t, modulus);
    }
  }
}

int main(int argc, char **argv) {
  unsigned long bits = 590069, index = 3056651345UL;
  if (argc == 2 && strcmp(argv[1], "--toy") == 0) {
    bits = 7;
    index = 77;
  } else if (argc != 1) {
    fprintf(stderr, "usage: %s [--toy]\n", argv[0]);
    return 2;
  }

  mpz_t modulus, x, q, z, t, u, gcd;
  mpz_inits(modulus, x, q, z, t, u, gcd, NULL);
  mpz_set_ui(modulus, 1);
  mpz_mul_2exp(modulus, modulus, 2 * bits);
  mpz_sub_ui(modulus, modulus, 1);
  mpz_set_ui(q, 1);
  mpz_mul_2exp(q, q, bits);
  mpz_set_ui(x, 1);
  mpz_mul_2exp(x, x, index % (2 * bits));
  /* q^3 ≡ q mod (q²−1), and X=2^index. */
  mpz_add_ui(z, x, 1);
  mpz_mul(z, z, q);
  mpz_mul_ui(z, z, 2);
  mpz_add_ui(z, z, 2);
  mpz_mod(z, z, modulus);

  matrix base, result, temporary;
  matrix_init(&base); matrix_init(&result); matrix_init(&temporary);
  mpz_set(base.e[0], z);
  mpz_sub_ui(base.e[1], modulus, 1); /* -1 modulo the modulus */
  mpz_set_ui(base.e[2], 1);
  mpz_set_ui(base.e[3], 0);
  mpz_set_ui(result.e[0], 1);
  mpz_set_ui(result.e[1], 0);
  mpz_set_ui(result.e[2], 0);
  mpz_set_ui(result.e[3], 1);

  unsigned long remaining = index;
  while (remaining != 0) {
    if (remaining & 1UL) {
      matrix_mul(&temporary, &result, &base, modulus, t, u);
      matrix_swap(&result, &temporary);
    }
    remaining >>= 1;
    if (remaining != 0) {
      matrix_mul(&temporary, &base, &base, modulus, t, u);
      matrix_swap(&base, &temporary);
    }
  }
  /* [[z,-1],[1,0]]^index has y_index(z) in the bottom-left entry. */
  mpz_gcd(gcd, result.e[2], modulus);
  gmp_printf("B=%lu r=%lu residue_bits=%zu gcd=%Zd\n", bits, index,
             mpz_sizeinbase(result.e[2], 2), gcd);
  int result_code = mpz_cmp_ui(gcd, 1) == 0 ? 0 : 1;
  matrix_clear(&base); matrix_clear(&result); matrix_clear(&temporary);
  mpz_clears(modulus, x, q, z, t, u, gcd, NULL);
  return result_code;
}
