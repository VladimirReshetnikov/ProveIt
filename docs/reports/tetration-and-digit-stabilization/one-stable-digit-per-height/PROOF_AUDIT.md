# Proof audit

This audit distinguishes a mathematical argument from finite verification.
It records the checks performed for the supplied article, not independent
peer review or a proof-assistant formalization.

## Domain and conventions

The main results use even q >= 4, a = q - 1, T_0 = 1, and
T_(h+1) = a^(T_h). All heights are nonnegative integers. Gaps are positive.
Towers are right-associated. The towers are strictly increasing and odd.
The q = 2 case is the constant base-1 tower and must be excluded from all
nonzero-distance formulas. The radix q is not the exponential base a.

For composite q, ord_q(x) = max{s : q^s divides x} is a precision order,
not a multiplicative valuation. The proof never assumes multiplicativity.

## Dependency graph

1. Elementary lifting lemma for principal units.
2. Specialization to a = q - 1 and even exponents.
3. Exact local distances between T_(h+r) and T_h.
4. Exact radix-q distance and the extra factor 2.
5. Binomial precision lemma and universal leading difference.
6. Sharp height threshold and the disproof/correction of C3.
7. Exponent period, contraction, unique fixed point and C1.
8. Two-digit binomial calculation and C2.
9. Compatible residues, digit lifting and modular algorithms.
10. Integer-tower representation of higher arrows and rank saturation.
11. Optional local Lambert formula with the correct sign at 2.

The Lambert section is not used anywhere in the elementary resolution.

## Local distances

Fix r >= 1 and D_h = T_(h+r) - T_h. Since all towers are odd and increase,
D_h is a positive even integer. At an odd prime p dividing q, D_0 is -2
modulo p, so v_p(D_0) = 0. At p = 2,

    v_2(D_0) = u = v_2(q - 2).

The exact recurrence is

    D_(h+1) = a^(T_h) * (a^D_h - 1).

The first factor is a unit at every prime dividing q. For even d > 0,

    v_p(a^d - 1) = v_p(q) + v_p(d)          (odd p | q),
    v_2(a^d - 1) = u + v_2(q) - 1 + v_2(d).

Thus

    v_p(D_h) = h*v_p(q)                    (odd p | q),
    v_2(D_h) = u + h*(u + v_2(q) - 1).

No cancellation between consecutive differences is assumed. The argument
works directly for each positive gap r. This is why the valuation is
independent of r.

## Composite-radix bottleneck

The formulas give 2*q^h | D_h. If q has an odd prime divisor p, then its
valuation is already too small for q^(h+1) | D_h. If q = 2^v, then v >= 2,
u = 1, and v_2(D_h) = 1 + h*v < (h+1)*v. This separate case is essential.

## First unstable digit

For d divisible by 2*q^h, expand (q - 1)^d = (1 - q)^d. The terms of degree
j >= 2 vanish modulo q^(h+2). For a prime p | q, use

    v_p(binomial(d,j)*q^j) >= j*v_p(q) + v_p(d) - v_p(j).

At odd p, v_p(j) <= j - 2. At 2, v_2(j) <= j - 1, and the extra factor 2
in d supplies the missing valuation. Therefore

    D_(h+1) == q*D_h       (mod q^(h+2)).

Since D_0 == -2 (mod q), induction gives the stated leading law. The
coefficient q - 2 describes the *difference* of the first unstable digits,
not the digit of the limiting number itself.

## C3 and its interpretation

The source states a congruence for j and then an equality with j. We take j
to be its least nonnegative representative, the strongest natural
interpretation for the conjecture. It still fails. For q >= 4 the difference
-2*q^m is nonzero modulo q^(m+1). The q = 2 column is trivial.

The witness uses only 3^27, which is easily constructed exactly. The
certificate records both residues, the integer difference and its exact
2-adic valuation. A repeated truncated value R_m = R_(m+1) does not mean
that the full tower T_m already has the next stable digit.

## Exponent reduction and uniqueness

Exponent reduction modulo an arbitrary output modulus is not assumed.
The explicit period a^(q^s) == 1 (mod q^(s+1)), s >= 1, is proved first.
If two odd exponents agree modulo q^s, applying a^x makes them agree modulo
q^(s+1). Any fixed-point residue is odd; repeated contraction proves
uniqueness. This also justifies the representative independence in C1 and
the digit-lifting algorithm R_(m+1) = a^(R_m) mod q^(m+1).

## Higher Knuth arrows

The normalization is H_1(n) = a^n, H_r(0) = 1, and
H_r(n+1) = H_(r-1)(H_r(n)). In particular H_r(1) = a.
At ranks r >= 2 there is an integer J_r(n) with H_r(n) = T_(J_r(n)).
For n >= 2, a >= 3, J_r(n) >= n + r - 2. Together with the sharp height
threshold, this gives an exact criterion through J and a practical
sufficient criterion through n + r - 2.

The rank inequality is not valid at base 2: 2 ↑^r 2 = 4 for every rank.
The code excludes that base in its capped-hyperoperation helper. The
zero- and one-argument cases are handled before saturation guards.

## Lambert sign and truncation

The branch sign is epsilon = +1 at p = 2 when q == 2 (mod 4), and -1
otherwise. With b = epsilon*(q-1), b is a principal unit, and
ell = log_p(b) has valuation >= 1 at odd p and >= 2 at p = 2.
The fixed point is -W_p(-epsilon*ell)/ell. Ordinary odd exponents retain
this sign. A logarithm extended by log_2(-1) = 0 would lose it.

At precision K, exact rational log and Lambert polynomials are truncated
after 2*(K+4)+4 terms. The article bounds all omitted terms beyond the
target precision and explains why substitution of the truncated log cannot
amplify its error. The rational denominator after summation is a p-adic
unit. This formula is checked against a separate totient-chain oracle.

## Verification independence and limitations

The general oracle uses phi(M) recursion. An exponent E >= phi(M) is
replaced by (E mod phi(M)) + phi(M); small exponents are obtained exactly by
capped evaluation. The article proves validity also for nonunits, using
phi(M) >= phi(p^e) >= e and the Chinese remainder theorem. The oracle is
checked against directly constructed integer towers before it is used to
check the specialized evaluator.

All 62,649 assertion checks pass, with 51,414 additional candidate classes
examined inside exhaustive fixed-point searches. This establishes the
recorded finite computations, not an exhaustive validation of all possible
software inputs. The infinite mathematical statements depend on their
proofs. No formal proof-assistant certificate is included.
