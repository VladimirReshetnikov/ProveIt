# Proof audit

This audit distinguishes a mathematical argument from finite verification. It
records the checks performed for the merged article, not independent peer review
or a proof-assistant formalization.

## Domain and conventions

Two settings run side by side and must not be interchanged.

**General setting.** `a` is an odd integer at least 3; `T_0 = 1`, `T_(h+1) = a^(T_h)`;
`D_h = T_(h+1) - T_h` and, for a gap r >= 1, `D_h^(r) = T_(h+r) - T_h`. Every tower
is odd and strictly increasing, so every difference is positive and even. A general
radix `R` is admissible only when every prime divisor of R divides a*a-1.

**Diagonal setting.** `B >= 4` is even and `a = B - 1`, with
`s = v_2(B-2) = v_2(a-1)`, `t = v_2(B) = v_2(a+1)`, `u = s + t - 1`. Exactly one of
s, t equals 1, and u >= t. The degenerate radix B = 2 has tower base 1 and constant
towers; it satisfies no nonzero-difference formula and is excluded everywhere. The
radix B is never the exponential base a.

Throughout, `q` denotes a **prime** and `v_q` a genuine valuation. For a composite
radix R, `ord_R(x) = max{j : R^j | x}` is a *precision order*, not a multiplicative
valuation: ord_6(2) = ord_6(3) = 0 but ord_6(6) = 1. No proof and no formula assumes
multiplicativity of ord_R; every digit count is written through prime valuations and
an explicit minimum.

## Logical chain

1. Odd-prime lifting is proved by a geometric-sum argument and binomial p-power steps.
2. Binary lifting is proved by factorization into successive square-plus-one factors.
3. D_h = a^(T_(h-1))*(a^(D_(h-1))-1) gives exact local affine valuation laws.
4. Strict growth of local valuations prevents cancellation in telescoping differences and proves permanent digit agreement.
5. For bases ending in 9, the two lines s+h*u and h*e give exact decimal stable counts.
6. Their crossing gives H=1 when e<=u, otherwise H=1+ceil(s/(e-u)).
7. Failure of H<=2 is equivalent to a=1 mod 4 and s<e<2*s.
8. Trial division certifies 2749; five congruence-restricted candidates prove minimality.
9. Exact CRT congruences force (s,t,e)=(s,1,s+1); coprimality of the CRT class and Dirichlet prove infinitely many prime examples with H=s+1.
10. Finite residue counting gives the density summands. A tail contained in v_2(a-1)>=S has relative density 2^(1-S), justifying the infinite union.
11. On the diagonal, steps 1–2 specialize to the exponent laws for even exponents, and a direct induction at fixed gap gives the gap-general local distances.
12. Those distances give the exact radix precision order ord_B(D_h^(r)) = h and the extra factor 2.
13. A binomial precision estimate plus induction gives D_h^(r) == -2*B^h (mod B^(h+1)) for every gap — the **shared core theorem**, proved once.
14. The core theorem gives the sharp threshold, with no earlier accidental visit.
15. An exponent-period and contraction lemma gives the fixed-point identity, uniqueness, compatibility across precisions, and the increasing-precision digit-lifting algorithm with its per-digit formula.
16. Compatibility gives the inverse limit xi_B and the exact distance from it.
17. Higher up-arrow thresholds follow from the exact tetration threshold, by the explicitly stated threshold recursion and, independently, by the tower-height representation.
18. The optional local Lambert formula follows from the inverse limit and established p-adic analysis. Nothing else depends on it.

## Two proofs kept, not one

Four conclusions are reached in the article by two genuinely different routes, and
both routes are retained and marked in the text.

- **Gap-independence of the local distances.** Telescoping plus the unique-minimum
  rule (general, any odd a) *and* a direct induction at fixed gap (diagonal only,
  but never forms the sum).
- **Uniqueness of the modular fixed point.** The dynamical theorem (orbit bounds m
  and m+1, sharp at starts 1 and 0, no other cycles) *and* a bootstrap that applies
  the contraction from B^0 upward. The dynamical theorem is strictly stronger and
  remains the headline; the bootstrap is kept because it is elementary and needs
  neither the core theorem nor any statement about orbits.
- **Higher-arrow saturation.** The exact threshold recursion for sigma_r(m) *and*
  the tower-height criterion through I_r(n), whose bound I_r(n) >= n+r-2 yields the
  checkable sufficient condition n+r-2 >= m — strictly stronger than sigma_r(m) <= m
  for every rank r > 2. The article derives the old bound *from* the new one.
- **The local Lambert formula.** Uniqueness of the small inverse branch *and* a
  direct verification by substitution using the strict contraction of
  x -> eps_q*Exp_q(ell_q*x).

The two independent modular oracles in the code are kept for the same reason.

## Composite-radix bottleneck

The diagonal formulas give 2*B^h | D_h^(r). If B has an odd prime divisor q, then
v_q(D_h^(r)) = h*v_q(B) < (h+1)*v_q(B), so that prime is the bottleneck and
B^(h+1) does not divide the difference. If B = 2^t, then t >= 2, s = 1, and
v_2(D_h^(r)) = 1 + h*t < (h+1)*t. This separate case is essential, and it is also
the reason excess powers of 2 never buy a whole extra radix digit.

## First unstable digit

For d divisible by 2*B^h, expand (B-1)^d = (1-B)^d. The terms of degree j >= 2
vanish modulo B^(h+2). For a prime q | B,

    v_q(binomial(d,j)*B^j) >= j*v_q(B) + v_q(d) - v_q(j).

The two prime cases must be stated separately.

- At odd q: v_q(j) <= j - 2 for every j >= 2. (If v_q(j) = k >= 1 then j >= 3^k >= k+2.)
- At q = 2: v_2(j) <= j - 1, and the **extra factor 2 in d** supplies the missing
  valuation.

Using the odd bound at q = 2 would be an outright error: v_2(2) = 1 > 0 = j - 2.
This is precisely why 2*B^h, and not merely B^h, is a hypothesis of the lemma.

Therefore D_(h+1)^(r) == B*D_h^(r) (mod B^(h+2)), and since D_0^(r) == -2 (mod B),
induction gives the stated leading law. The coefficient B - 2 describes the
**difference** of the first unstable digits, not the digit of the limiting number
itself; digits farther left can also change, and carries must not be ignored.

## C3 and its interpretation

The source states a congruence for j and then an equality with j. We read j as its
least nonnegative representative — the strongest natural interpretation available to
the conjecture, since literal equality with an arbitrary congruent integer would
already be meaningless. It still fails. For B >= 4 the difference -2*B^m is nonzero
modulo B^(m+1). The B = 2 column (n = 1) is trivially true and is separately
acknowledged as degenerate.

The witness uses only 3^27, which is easily constructed exactly, and is also
hand-checkable: 3^8 == 33, 3^16 == 1, so 3^27 == 1*33*9*3 == 59 (mod 64). The
certificate records both residues, the integer difference and its exact 2-adic
valuation.

A repeated truncated value R_m = R_(m+1) does **not** mean that the full tower T_m
already has the next stable digit. At B = 4, R_3 = R_4 = 59 while T_3 == 187
(mod 256). Confusing R_m with T_m would conceal the very discrepancy that refutes C3.

## Exponent reduction and uniqueness

Exponent reduction modulo an arbitrary output modulus is not assumed, and there are
two distinct failure modes in general: the iteration can settle into a cycle that is
not the tower (a = 2, M = 7 gives 1,2,4,2,4,... while T_4(2) == 2 mod 7), and
exponents may not be reducible at all (2^3 is not congruent to 2^(3+3) modulo 3).

The explicit period a^(B^s) == 1 (mod B^(s+1)) is proved first. If two odd exponents
agree modulo B^j, with j >= 0, applying a^x makes them agree modulo B^(j+1). Any
fixed-point residue is odd; repeated contraction proves uniqueness. This also
justifies representative independence in C1 and the digit-lifting recurrence
R_(m+1) = a^(R_m) mod B^(m+1).

## Higher Knuth arrows

The normalization is U_1(a,n) = a^n, U_r(a,0) = 1, U_r(a,n+1) = U_(r-1)(a,U_r(a,n)),
so U_2(a,n) = T_n and U_r(a,1) = a. At ranks r >= 2 there is an integer I_r(n) with
U_r(a,n) = T_(I_r(n)), and for n >= 2, a >= 3, I_r(n) >= n + r - 2. Together with the
sharp height threshold this gives an exact criterion through I and a practical
sufficient criterion through n + r - 2 >= m.

I_r(n) is **not** J_R(m), the first permanent height modulo R^m in the general-radix
theorem; the two symbols are unrelated and both appear in the article.

The rank inequality is not valid at base 2: 2 ↑^r 2 = 4 for every rank. The code
excludes that base in its capped-hyperoperation helper. The zero- and one-argument
cases are handled before the saturation guards.

## Lambert sign and truncation

The branch sign is eps = +1 at q = 2 when B == 2 (mod 4), and -1 otherwise. With
b = eps*(B-1), b is a principal unit, and ell = Log_q(b) has valuation >= 1 at odd q
and >= 2 at q = 2. The fixed point is -W_q(-eps*ell)/ell. Ordinary odd exponents
retain this sign; a logarithm extended by Log_2(-1) = 0 would lose it, and a blind
minus sign at both primes gives the wrong 2-adic branch (worked out at B = 6).

At precision K, exact rational log and Lambert polynomials are truncated after
2*(K+4)+4 terms. The article bounds all omitted terms beyond the target precision,
and explains why substituting the truncated logarithm cannot amplify its error: the
linear coefficient of the fixed-point series is 1, and on principal-unit domains no
higher power magnifies an input error. The rational denominator after summation is a
q-adic unit. In the truncation estimates the symbol `kappa = v_q(b-1)` is used, kept
distinct from the global s = v_2(B-2). This formula is checked against the general
totient-chain oracle.

## Scope checks

- The prime conjecture in the original source includes every prime ending in 9: n=1 is allowed.
- The source's V(a,h) equals C(h)-C(h-1). The disproof is at h=2, not at a shifted height.
- An integer ending in 9 can be 1 or 3 modulo 4. Setting s=1 universally would be a fatal error.
- At an integer crossing of the two valuation lines, the final above-limit speed is still present at that crossing. The first permanent speed occurs one height later.
- B=2 has tower base 1 and zero differences; it is excluded from the diagonal theorems. The OEIS column n=1 is separately acknowledged as degenerate.
- Composite-radix divisibility exponents are **defined** as a precision order ord_R, with the non-multiplicativity example given once, and are never treated as valuations. The case split that computes ord_B exactly is proved.
- General-radix affine formulas require all prime divisors of R to divide a*a-1 and allow arbitrary odd a; the diagonal theorems require a = B-1 with even B >= 4. No statement proved in one setting is asserted in the other.
- The density theorem samples all integers ending in 9, not primes.
- Neither arbitrary modular-tetration evaluation nor continuous tetration is claimed. xi_B is an inverse limit of residues, **not** a real infinite tower: since a >= 3 the real tower diverges, and only the modular tails converge.
- The restricted family a = B-1 is why none of this is an unrestricted fast modular-tetration algorithm; Hittmeir's reduction of squarefree-part computation to general modular tetration marks the boundary.
- A finite test suite does not prove universal assertions or formal correctness of these English proofs.
- Nothing has been submitted to OEIS by this work.

## Independence of numerical checks

Validation is in three layers, so that no test reuses the routine it is meant to
check.

1. **Literal integers.** Directly constructed, manageable integer towers.
2. **Two independent oracles.** A restricted Euler chain reduces exponents modulo
   phi(M) on {2,5}-supported moduli with unit bases. A general totient chain handles
   arbitrary moduli and nonunit bases: an exponent E >= P = phi(M) is replaced by
   (E mod P) + P; at a prime power p^f | M with p dividing the base, both exponents
   are at least P >= phi(p^f) >= f, so both powers vanish mod p^f, and CRT finishes.
   Small exponents are obtained exactly by capped evaluation. Both oracles are
   checked against the literal integers and against each other; the capped lift is
   also checked directly on nonunit bases.
3. **Specialized evaluators.** Only then are the fixed-modulus iterator, the
   digit-lifting routine, and the higher-arrow evaluator checked against the oracles.

The main residue iterator additionally checks the sufficient exponent-period
condition a^M == 1 mod M before iterating, and rejects unsupported pairs. A concrete
rejection case tests the guard, and a known-bad iteration is exercised to confirm it
really fails.

The valuation checks use nonzero residues at precision strictly above both predicted
local valuations. For primality, the main example has a complete small
trial-divisor certificate; all other displayed example primes are deterministically
checked by trial division, and the list below 100000 is generated by a sieve.

The merged run passes 183,204 exact assertions — 118,813 from the decimal families
and 64,391 from the diagonal families — plus 51,414 residue classes examined inside
exhaustive fixed-point searches and deliberately not counted as assertions. The two
subtotals count assertions *executed*, not distinct facts: the grids overlap on even
radices 4..100 at heights 0..10, so they must not be added, and neither of the two
originally published totals (118,271 and 62,649) is the merged total. This
establishes the recorded finite computations, not an exhaustive validation of all
possible software inputs. The infinite statements depend on their proofs. No formal
proof-assistant certificate is included.

## Literature limitations

The eventual-speed formula is prior work, not claimed as new. The later paper by
Ripà and Onnis was checked for its formulas and discussion of transients. General
modular stabilization, lifting-the-exponent arguments, and the p-adic Lambert W
function are established background; Hittmeir and Mező are cited for that context
and not as sources of any proof here.

No explicit prior resolution of the selected prime conjecture, and none of the three
A324017 statements, was located by the targeted searches, but this is not an
exhaustive literature certificate. The principal statements in this note are
mathematically proved as written; their originality remains unverified.
