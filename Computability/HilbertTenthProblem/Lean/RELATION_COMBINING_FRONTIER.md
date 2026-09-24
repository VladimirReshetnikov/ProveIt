# Relation combining: constructions and degree certificates

This guide, updated 2026-09-14, distinguishes the original common-weight
construction, the refined six-square and five-square constructions, and
the positive-padding construction of exact degree 13697. The refined
degree and application proofs pass the consolidated build and transitive
axiom audits. The receipt and earlier milestones are recorded in
[STATUS.md](STATUS.md).
The original common-weight estimates 148864 and 297729 below remain
source-derived calculations; the refined degree certificates do not verify
those older estimates.

The original implementation uses six square conditions and the common
weight `W = 1 + Σ Aᵢ²`, with the squared `B², C²` version of relation
combining. Its definitions are in
[TwelveVariablePolynomial.lean](Diophantine/Paper1976/TwelveVariablePolynomial.lean):
`capitals`, `radicands`, `marginPolynomial`, `combined`, and `primePolynomial`.
The last is `(k + 2) * (1 - combined²)` on twelve natural coordinates.

The refined source has separate definitions in
[RefinedTwelveVariablePolynomial.lean](Diophantine/Paper1976/RefinedTwelveVariablePolynomial.lean)
and [FiveSquarePrimePolynomial.lean](Diophantine/Paper1976/FiveSquarePrimePolynomial.lean).
[RefinedPolynomialDegrees.lean](Diophantine/Paper1976/RefinedPolynomialDegrees.lean)
provides their degree bounds, while
[ExactDegreePrimePolynomial.lean](Diophantine/Paper1976/ExactDegreePrimePolynomial.lean)
defines the padding construction. All use the same twelve natural coordinates;
weights and capital letters are polynomial substitutions.

The corrected article is
[Papers/1976/jones1976_corrected.tex](../Papers/1976/jones1976_corrected.tex),
§3 after Theorem 3.9, currently lines 958–999. The relevant landmarks are the
denominator-cleared form of (XIV), the paragraphs defining the degrees of
`M₆`, and the replacement square condition (24). The original general
relation-combining formula is on
[Matiyasevich–Robinson (1975), p. 526](https://logic.pdmi.ras.ru/~yumat/papers/23_paper/page526.gif),
with its common weight on
[p. 527](https://logic.pdmi.ras.ru/~yumat/papers/23_paper/page527.gif).

## Original common-weight construction: source bounds 148864 and 297729

Give each of the twelve coordinates degree one. Replacing the article's
parameter `k` by `k + 1` does not increase any bound. The capital substitutions
give the following degree upper bounds:

| Capital | M | A | B | C | D | E | F | G | H | I | K | L | R | S |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree bound | 3 | 4 | 1 | 1 | 10 | 13 | 34 | 68 | 2 | 140 | 4 | 5 | 6 | 2 |

For example, `D = (A² - 1)C² + 1` has bound `2·4 + 2·1 = 10`,
`E = 2(i+1)DC²` has bound `1 + 10 + 2 = 13`, and
`I = (G² - 1)H² + 1` has bound `2·68 + 2·2 = 140`.

The six radicands, in the implemented order (I), (II), (VII), (XV), (XVI),
(XVII), consequently have bounds

`δ = [6, 6, 184, 14, 18, 22]`.

The large entry is `deg(DFI) ≤ 10 + 34 + 140 = 184`; thus `deg W ≤ 368`.
For the cleared inequality put

```
den = (C - (w+1)xKL)(C-R)²
num = RKC²
margin = den² - 4(num - (S+1)den)².
```

The bounds are `deg den ≤ 23`, `deg num ≤ 12`, and `deg margin ≤ 50`.
The divisibility parameters in the combining theorem are `Bdiv = F` and
`Cdiv = H-C`, with bounds 34 and 2. These must not be confused with the
article's capital `B` and `C`.

Assign each formal radical weight `δᵢ/2`, which is integral in all six cases.
The weighted degree of each signed factor is at most

```
max(2·34 + 1, 2·2,
    2·34 + 50 + max(2·2, 6·368, maxᵢ(δᵢ/2 + i·368)))
= 68 + 50 + 2208
= 2326,
```

where `i = 0,…,5`. The largest radical-term bound is `11 + 5·368 = 1851`,
strictly below 2208. There are `2⁶ = 64` factors. Removing even radical
exponents and substituting the actual radicands preserves this degree bound:

```
deg combined ≤ 64·2326 = 148864
deg primePolynomial ≤ 1 + 2·148864 = 297729.
```

This source calculation reproduces the article's first `M₆` number and
supplies a weaker bound for the original prime polynomial. Neither 148864
nor 297729 is claimed here as a Lean-certified bound. The refined and padded
polynomials below are separately defined constructions.

## Refined six-square construction: upper bound 13376

The explicit refined product in
[RefinedRelationCombiningPolynomial.lean](Diophantine/Common/RefinedRelationCombiningPolynomial.lean)
is

```
P₀ = 1,   Pᵢ = V₁⋯Vᵢ,
∏ε [Bdiv·t + Cdiv - Bdiv(2·margin-1)
       (Cdiv + Pq + Σᵢ εᵢ√Aᵢ Pᵢ₋₁)].
```

The unsquared version applies here because `F > 0` and `H-C > 0` on every
natural assignment; see `elim39Values_divisibility_positive` in
[Theorem39Elimination.lean](Diophantine/Paper1976/Theorem39Elimination.lean).
The theorem in
[RefinedRelationCombining.lean](Diophantine/Common/RefinedRelationCombining.lean)
retains `Vᵢ ≥ 1 + |√Aᵢ|`. Its prefix bound is
`Σᵢ≤j |√Aᵢ|Pᵢ₋₁ ≤ Pj - 1`, by telescoping. The necessity argument permits
signed and repeated radicands and zero roots; it uses automorphisms and
norm separation rather than independence of square classes. The empty
family has offset one and remains covered.

Polynomial bounds for the `Vᵢ` must hold on **all natural assignments**, not
just intended solutions. In particular, `K`, `L`, and `R` can be negative;
when `x=0`, for example, `Mx-1=-1`. Safe polynomial majorants, expressed with
the article's parameter `k`, are

```
K# = n+k+1 + p(M+1)
L# = k+1 + l(Mx+1)
R# = k+1 + r(Mnx+1)
G# = A + F(F+A).
```

They bound `|K|, |L|, |R|, |G|` and have bounds 4, 5, 6, 68 respectively.
The other capitals needed below, including `M,A,C,D,E,F,H`, are nonnegative
on every natural assignment. The elementary complex-modulus estimate

`1 + |√((α²-1)β²+1)| ≤ |αβ| + |β| + 2`

holds even when the radicand is negative. It yields these explicit choices:

| Radicand | Safe polynomial `V` | Degree bound |
|---|---|---:|
| `U(2k,n)` | `(2k+4)(2k+2)(n+1)+2` | 3 |
| `U(2n,x)` | `(2n+4)(2n+2)(x+1)+2` | 3 |
| `DFI` | `((A+1)C+2)((A+1)E+2)((G#+1)H+2)` | 92 |
| `(M²-1)K²+1` | `(M+1)K#+2` | 7 |
| `((Mx)²-1)L²+1` | `(Mx+1)L#+2` | 9 |
| `((Mnx)²-1)R²+1` | `(Mnx+1)R#+2` | 11 |

For `DFI`, the three factor bounds have degrees 5, 17, 70; their product is
at least `1 + |√(DFI)|`. For the first two entries use the Pell form of
`U(a,b)` with `α=a+3`, `β=(a+2)(b+1)`.

The six degree bounds sum to 125. Each refined signed factor has weighted
degree at most `34 + 50 + 125 = 209`. Therefore

`deg M₆ ≤ 64·209 = 13376`.

The corresponding prime-polynomial bound is `1 + 2·13376 = 26753`.
The concrete certificate APIs are
`JSWW1976.RefinedPolynomialDegrees.totalDegree_six_combined` and
`totalDegree_six_primePolynomial`.

## Five squares: upper bounds 6848 and 13697

Put `T = U(2k,n)`. Condition (24) replaces the first two tests by

`T [16T(T-1)(n+1)²(x+1)² + 1] = square`.

The product radicand has degree bound `6 + 16 = 22`. A safe refined weight is

`Vnew = ((2k+4)(2k+2)(n+1)+2) · (4T(n+1)(x+1)+2)`,

with degree bound `3 + 8 = 11`. Its second factor is the Pell majorant for
`α=2T-1`, `β=2(n+1)(x+1)`. Thus the five weight bounds are
`[11,92,7,9,11]`, with sum 130, and there are only 32 sign factors:

```
deg M₅ ≤ 32·(34+50+130) = 6848
deg ((k+2)(1-M₅²)) ≤ 1+2·6848 = 13697.
```

The concrete certificate APIs are
`JSWW1976.RefinedPolynomialDegrees.totalDegree_five_combined` and
`totalDegree_five_primePolynomial`. The semantic proof in
[FiveSquareGrowth.lean](Diophantine/Paper1976/FiveSquareGrowth.lean) and
[FiveSquareCriterion.lean](Diophantine/Paper1976/FiveSquareCriterion.lean)
uses four steps:

1. The factors in (24) are coprime, since the second is 1 modulo `T`.
   Hence a square product forces both factors to be squares.
2. The first factor supplies the original lower bound on `n`. For the
   second, write `2(n+1)(x+1)=ψ_(2T-1)(j)`. Divisibility gives
   `2(n+1) ∣ j`; positivity gives `j>0`, hence `j≥2(n+1)`. Pell growth
   then implies `x>(2n)^(2n)`.
3. Conversely, for each admissible `n`, Pell coordinates divisible by
   `2(n+1)` supply arbitrarily large natural `x` satisfying (24).
4. `theorem_3_9_sufficiency_of_growth` accepts those growth hypotheses on
   `n,x`. `theorem_3_9_necessity_of_growth` constructs all remaining
   witnesses for supplied sufficiently large `n,x`; it does not require
   the original second square condition.

The five-square condition does **not** assert `U(2n,x)` is a square for the
same `x`. Consequently it cannot be fed directly into
`ReducedSys39`, whose first two radicands retain exactly those square tests.
`FiveSquareSys39` supplies the separate criterion using the exposed growth
interface. It retains ten natural witnesses; the combining witness and
prime parameter bring the polynomial to twelve coordinates. The shift
from article parameter `k` to `k+1` includes prime 2 at outer coordinate 0.

## Exact degree by positive padding

The unpadded five-square combined polynomial `M` has the degree bound
`M.totalDegree ≤ 6848`; counting signed factors does not establish equality.
The exact-degree construction instead sets

```
e = 6848 - M.totalDegree
Mpad = (X 11 + 1)^e * M
Ppad = (X 0 + 2) * (1 - Mpad²).
```

The padding factor is positive on every natural assignment, including when
`e=0`, so `Mpad` and `M` have exactly the same natural zero set. The combined
polynomial is nonzero: if it vanished identically, the prime-value theorem
would make 4 prime. Additivity of total degree for nonzero products gives
`deg Mpad = 6848`, then `deg Ppad = 13697`. Its positive natural-assignment
values are exactly the primes, with no added coordinate. The APIs are
`JSWW1976.ExactDegreePrimePolynomial.totalDegree_paddedCombined`,
`totalDegree_primePolynomial`, and `exists_exact_degree_prime_polynomial`.

This establishes the literal exact-degree existence assertion through
positive padding. It does not establish equality for the unpadded `M`, nor
does it assert that padding changes the polynomial when `e=0`.

## Degree calculus and substitution interfaces

[RefinedRelationCombiningDegree.lean](Diophantine/Common/RefinedRelationCombiningDegree.lean)
first substitutes the weight and arithmetic parameters into the actual
target polynomial ring. Its `ScaledBound` invariant bounds

`2 * (p.coeff d).totalDegree + Finsupp.weight dA d`

on every supported outer monomial. Closure under sums and products bounds
all sign factors uniformly. `totalDegree_eval₂_le_of_expand_bound` then
uses the coefficient identity for `expand 2` to transfer the bound through
exponent halving and arbitrary radicand substitutions. Polynomial-valued
coefficients retain their full degrees throughout this calculation.

The practical theorem `totalDegree_compose_le` assumes
`dA i ≤ 2*dV i` and `dn ≤ dD + max dC (Σ i, dV i)` and gives

`deg(compose q A V n b c d) ≤ 2^q * (dB + dD + max dC (Σ i, dV i))`.

The degree vectors are `[6,6,184,14,18,22]` for the six radicands and
`[3,3,92,7,9,11]` for their weights, or `[22,184,14,18,22]` and
`[11,92,7,9,11]` after merging the first two square tests. The arithmetic
parameter bounds are `[dn,dB,dC,dD]=[1,34,2,50]`. The numerical wrappers
`totalDegree_compose_six_le` and `totalDegree_compose_five_le` supply the
bounds 13376 and 6848 without expanding 64 or 32 signed factors.

Useful inspected Mathlib APIs, relative to `.lake/packages/mathlib/Mathlib/`:

- `Algebra/MvPolynomial/Degrees.lean`: `totalDegree_add` (473),
  `totalDegree_mul` (503), `totalDegree_pow` (511),
  `totalDegree_finsetProd` (541), `totalDegree_finsetSum` (547).
- `Algebra/MvPolynomial/CommRing.lean`: `totalDegree_neg` (185),
  `totalDegree_sub` (188).
- `Algebra/MvPolynomial/Expand.lean`: `coeff_expand_smul` (81),
  `support_expand` (182), `totalDegree_expand` (187).
- `Algebra/MvPolynomial/NoZeroDivisors.lean`:
  `totalDegree_mul_of_isDomain`, used for exact degree after padding.
- `RingTheory/MvPolynomial/WeightedHomogeneous.lean`:
  `weightedTotalDegree` (96), `le_weightedTotalDegree` (118).
- `RingTheory/MvPolynomial/Homogeneous.lean`: `weightedTotalDegree_one` (63).

This frontier concerns shared relation combining and the 1976 article only.
It makes no assertion about the separately progressing 1980 formalization.
