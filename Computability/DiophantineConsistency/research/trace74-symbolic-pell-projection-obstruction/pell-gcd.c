/* Exact modular Pell calculation for the fixed scalar candidate.
 *
 * Computes gcd(y_r(z), 2^(2B)-1) without constructing y_r(z), where
 * B=590069, r=3056651345, z=2*q*(X+1)+2, q=2^B and X=2^r.
 * The reduction uses q^2=1 and 2^r=2^(r mod 2B) modulo the modulus.
 * GMP is an external computation, not a Lean proof or graph-zero check.
 */
#include <gmp.h>
#include <stdio.h>

int main(void) {
    const unsigned long B = 590069UL, r = 3056651345UL;
    mpz_t M, z, X, q, U, V, A, C, T, S, G;
    mpz_inits(M, z, X, q, U, V, A, C, T, S, G, NULL);
    mpz_set_ui(M, 1); mpz_mul_2exp(M, M, 2 * B); mpz_sub_ui(M, M, 1);
    mpz_set_ui(q, 1); mpz_mul_2exp(q, q, B);
    mpz_set_ui(X, 1); mpz_mul_2exp(X, X, r % (2 * B));
    mpz_add_ui(z, X, 1); mpz_mul(z, z, q); mpz_mul_ui(z, z, 2);
    mpz_add_ui(z, z, 2); mpz_mod(z, z, M);
    mpz_set_ui(U, 0); mpz_set_ui(V, 1);
    /* Loop invariant before each bit: U=y_k(z), V=y_(k+1)(z) mod M. */
    int top = 8 * (int)sizeof(r) - 1;
    while (top > 0 && !(r & (1UL << top))) --top;
    for (int i = top; i >= 0; --i) {
        /* y_(2k)=y_k(2y_(k+1)-z*y_k), y_(2k+1)=y_(k+1)^2-y_k^2. */
        mpz_mul(T, z, U); mpz_mul_ui(S, V, 2); mpz_sub(T, S, T);
        mpz_mul(A, U, T); mpz_mod(A, A, M);
        mpz_mul(C, V, V); mpz_mul(T, U, U); mpz_sub(C, C, T); mpz_mod(C, C, M);
        if ((r >> i) & 1UL) {
            mpz_set(U, C); mpz_mul(T, z, C); mpz_sub(T, T, A); mpz_mod(V, T, M);
        } else {
            mpz_set(U, A); mpz_set(V, C);
        }
    }
    mpz_gcd(G, U, M);
    gmp_printf("B=%lu r=%lu residue_bits=%zu gcd=%Zd\n", B, r, mpz_sizeinbase(U, 2), G);
    int ok = mpz_cmp_ui(G, 1) == 0;
    mpz_clears(M, z, X, q, U, V, A, C, T, S, G, NULL);
    return ok ? 0 : 1;
}
