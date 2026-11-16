# iPRA derivations of theorems from the proof packets

This directory holds actual derivations, in intuitionistic primitive recursive
arithmetic, of theorems whose proofs are outlined in the research packets of
[`docs/proofs/`](../docs/proofs/README.md).

The derivations are in the embedded calculus `Prf PRAAx` of
[`ConciseIPRA`](../ConciseIPRA/README.md). This is iPRA in its usual
form: a function symbol for every primitive recursive definition, its defining
equations, the successor axioms, and induction for quantifier-free formulas, over
intuitionistic natural deduction with equality. Every theorem here has the type

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] φ
```

for an explicit iPRA sentence `φ`, and is checked by Lean's kernel. Through
`ConciseIPRA`'s transfer theorem `pra_iff_native` each one is also a theorem of
the native scalar core. The audit file
[`Checks/Axioms.lean`](Lean/IPRADerivations/Checks/Axioms.lean) prints the
axioms of every listed theorem; they are Lean's standard `propext`,
`Quot.sound` and `Classical.choice`, which are used in the metatheory, and no
`sorry`.

The Lake library is `IPRADerivations` (namespace `LeanProofs.IPRA`), built with

```bash
lake build IPRADerivations
```

## Layout

The library is built bottom-up. Reusable layers come first:

| Module | Contents |
|---|---|
| [`Core/Basic`](Lean/IPRADerivations/Core/Basic.lean) | Symbols for `+`, `*`, predecessor and truncated subtraction, their defining equations at arbitrary terms, congruence, quantifier-free induction on an open formula (`ind`), and instantiation of closed derivations (`inst`) |
| [`Core/Semiring`](Lean/IPRADerivations/Core/Semiring.lean) | The commutative-semiring laws, additive cancellation and the successor axioms at arbitrary terms, each derived by induction |
| [`Core/Quotient`](Lean/IPRADerivations/Core/Quotient.lean) | Terms modulo provable equality under a context `Γ` form a cancellative commutative semiring `Q Γ` |
| [`Core/Integers`](Lean/IPRADerivations/Core/Integers.lean) | Integers as differences: integer terms `ZT` with their iPRA equation `ZT.eq`, and the ring of differences `Groth (Q Γ)`, in which integer identities are proved by `ring` and `linear_combination` |
| [`Core/Tactic`](Lean/IPRADerivations/Core/Tactic.lean) | Universal closures `allN` and `univ`, and the tactic `ipra_ring` for polynomial identities |
| [`Core/Definitions`](Lean/IPRADerivations/Core/Definitions.lean) | `toPR`, the symbol computing an open term; definitions by primitive recursion from a base and a step term, with their equations; finite sums and products, powers and factorials |
| [`Core/Sums`](Lean/IPRADerivations/Core/Sums.lean) | Theorems with the summation bound as an iPRA variable, by induction: Gauss's sum, the sum of odd numbers, telescoping for every unary symbol `f`, and summation by parts (Abel, used by `von_mangoldt_totient_ipra_2026-11-15`) for all unary symbols `a`, `b` |
| [`Core/Monus`](Lean/IPRADerivations/Core/Monus.lean) | Truncated subtraction: `0 ∸ b = 0`, `Sa ∸ Sb = a ∸ b`, `(a + b) ∸ b = a`, `a ∸ (a + c) = 0`, zero-or-successor, and the joint induction giving `(a ∸ b) + b = (b ∸ a) + a` and `(a ∸ b)(b ∸ a) = 0` |
| [`Core/Order`](Lean/IPRADerivations/Core/Order.lean) | `a ≤ b` as `a ∸ b = 0` and `a < b` as `S a ≤ b`: witnesses `b = a + d`, reflexivity, transitivity, antisymmetry, totality, `lt_or_le`, decidability of equality, monotonicity of `+` and `*`, and cancellation |
| [`Core/Pairing`](Lean/IPRADerivations/Core/Pairing.lean) | The equality test `eqb`; the integer square root by primitive recursion, with `isqrt z² ≤ z < (isqrt z + 1)²` and uniqueness; the pairing `⟨a, b⟩ = (a + b)² + a` with projections; simultaneous primitive recursion of two sequences, with both pairs of equations |
| [`Core/Powers`](Lean/IPRADerivations/Core/Powers.lean) | `a^{m+k} = aᵐ aᵏ`, `a ≤ b → aᵐ ≤ bᵐ`, `S a ≤ (S a)^{S m}`, and no square strictly between `k²` and `(k + 1)²` |
| [`Core/Parity`](Lean/IPRADerivations/Core/Parity.lean) | `par` and `half` by recursion; `x = 2 half x + par x`, `x` even or odd, `par (2k) = 0`, `par (2k + 1) = 1`, and `2k ≠ 2m + 1` |
| [`Core/BoundedSums`](Lean/IPRADerivations/Core/BoundedSums.lean) | Sums of terms as bounded universal quantifiers: a zero sum has zero terms below its bound, and terms that are zero for every index give a zero sum |
| [`Core/Descent`](Lean/IPRADerivations/Core/Descent.lean) | Generic infinite descent: an indicator `χ(a, b)` with a solution bound `a < β(b)` and a step from a solution with `b ≠ 0` to a smaller one is refutable; proved by induction on the count of solutions with `b < N` |
| [`Core/Division`](Lean/IPRADerivations/Core/Division.lean) | Remainder and quotient by recursion on the dividend; for `K ≥ 1`, `z = K quo z + rem z` with `rem z < K`, and uniqueness of quotient and remainder |
| [`Core/Gcd`](Lean/IPRADerivations/Core/Gcd.lean) | Divisibility as `rem x d = 0`, with closure under sums, multiples and differences and cancellation of a positive factor in `≤`; the Euclidean algorithm as a simultaneous recursion, its termination within `b + 1` steps, preservation of common divisors, and the gcd theorem: every common divisor divides `gcd(a, b)`, which divides `a` and `b` when positive (used by `mordell_weil_ipra`, `ipra_categorical_methods`) |
| [`Core/Search`](Lean/IPRADerivations/Core/Search.lean) | Bounded search `μ_{i<N} [f(i, x) = 0]` by primitive recursion, with its specification: a zero below `N` is found, at or before it, and no earlier index is a zero |
| [`Core/SumLemmas`](Lean/IPRADerivations/Core/SumLemmas.lean) | Index shift, additivity, congruence under a bounded hypothesis (with different parameters), and `term ≤ sum` |
| [`Core/Bezout`](Lean/IPRADerivations/Core/Bezout.lean) | The extended Euclidean algorithm with sign-free coefficients and a parity, frozen after termination, and Bézout's identity with natural coefficients: `gcd(a, b) + v b = u a` or `gcd(a, b) + u a = v b` |
| [`Core/EuclidLemma`](Lean/IPRADerivations/Core/EuclidLemma.lean) | The gcd theorems and Bézout's identity at arbitrary terms; `gcd(a, b) = 0 → a = 0`; `d ∣ x, x ≥ 1 → d ≤ x`; `gcd(p, a) = 1` for a prime `p ∤ a`; Euclid's lemma `prime p → p ∣ ab → p ∣ a ∨ p ∣ b` (uses `prime` from `AnalyticNumberTheory/Primes`) |
| [`Core/LinearAlgebra`](Lean/IPRADerivations/Core/LinearAlgebra.lean) | Integer vectors and matrices: finite sums, dot and cross products, matrix products, traces, determinants by Laplace expansion and adjugates by cofactors, each evaluated to the corresponding Mathlib operation; matrix equations as finite conjunctions |

The theorem modules are grouped by the areas of `docs/proofs/`:

| Module | Packet | Theorems |
|---|---|---|
| [`Algebra/CayleyHamilton`](Lean/IPRADerivations/Algebra/CayleyHamilton.lean) | [`cayley_hamilton_ipra`](../docs/proofs/algebra/cayley_hamilton_ipra/) | Cayley–Hamilton for 2×2 and 3×3 integer matrices; `M · adj M = (det M) I` and `det (M N) = det M · det N` as schemas, one theorem for every size; `L(q r) = L(q) L(r)` for quaternions and Euler's four-square identity |
| [`Algebra/CubeRootTwo`](Lean/IPRADerivations/Algebra/CubeRootTwo.lean) | [`three_impossibilities_ipra`](../docs/proofs/algebra/three_impossibilities_ipra/) | `X³ − 2` has no rational root: `a³ = 2b³ → b = 0`, by 2-adic infinite descent, organised as induction on `N` for the vanishing of the count `T(N) = ∑_{b<N} ∑_{a≤2b} [a³ = 2b³ ∧ b ≠ 0]` |
| [`Algebra/TrisectionCubic`](Lean/IPRADerivations/Algebra/TrisectionCubic.lean) | [`three_impossibilities_ipra`](../docs/proofs/algebra/three_impossibilities_ipra/) | `Y³ − 3Y − 1` (satisfied by `2 cos 20°`) has no rational root: both sign cases `a³ = 3ab² + b³` and `3cb² = c³ + b³` force `b = 0`, by the generic 2-adic descent |
| [`Algebra/PolynomialFormulas`](Lean/IPRADerivations/Algebra/PolynomialFormulas.lean) | [`ipra_polynomial_formulas_abel_ruffini`](../docs/proofs/algebra/ipra_polynomial_formulas_abel_ruffini/), [`three_impossibilities_ipra`](../docs/proofs/algebra/three_impossibilities_ipra/) | The quadratic, Cardano and Ferrari factorisations as implications from the defining relations of the radicals and of `ω`; the triple-angle identity on the unit circle |
| [`AnalyticNumberTheory/Primes`](Lean/IPRADerivations/AnalyticNumberTheory/Primes.lean) | the prime-counting packets (`pnt_ipra_constructive_2026-11-14`, `prime_distribution_ipra`, `brun_ipra_2026-11-15`) | The least factor `lpf z ≥ 2` of `z ≥ 2` divides `z` and is prime; `1 ≤ d ≤ m → d ∣ m!`; Euclid's theorem: `lpf(n! + 1)` is a prime greater than `n` |
| [`AnalyticNumberTheory/Fermat`](Lean/IPRADerivations/AnalyticNumberTheory/Fermat.lean) | [`von_mangoldt_totient_ipra_2026-11-15`](../docs/proofs/analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15/) | Fermat's little theorem `prime p → aᵖ ≡ a (mod p)` (the prime case of `thm:euler`), via the absorption identity `(j + 1) C(q + 1, j + 1) = (q + 1) C(q, j)`, `p ∣ C(p, k)` for `0 < k < p` (by Euclid's lemma), and the freshman's dream `(a + 1)ᵖ ≡ aᵖ + 1 (mod p)` |
| [`AnalyticNumberTheory/RSA`](Lean/IPRADerivations/AnalyticNumberTheory/RSA.lean) | [`von_mangoldt_totient_ipra_2026-11-15`](../docs/proofs/analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15/) | Fermat's theorem for units `prime p → p ∤ a → a^{p−1} ≡ 1 (mod p)` (the prime case of `thm:euler`); `x^{1 + k(p−1)} ≡ x (mod p)`; `(xᵉ)ᵈ = x^{ed}`; distinct primes are coprime; RSA correctness (`thm:rsa`): for distinct primes `p, q` and `ed = 1 + t(p − 1)(q − 1)`, `(xᵉ)ᵈ ≡ x (mod pq)`, via the CRT uniqueness of `Foundations/ChineseRemainder` |
| [`Analysis/Chebyshev`](Lean/IPRADerivations/Analysis/Chebyshev.lean) | [`trigonometric_identities_ipra_2026-11-15`](../docs/proofs/analysis/trigonometric_identities_ipra_2026-11-15/) | For `X = w + 1` and every `n`: `T_n² = (X² − 1) U_{n−1}² + 1` by induction, and `T_{n+2} + T_n = 2X T_{n+1}` |
| [`Analysis/Products`](Lean/IPRADerivations/Analysis/Products.lean) | [`bohr_mollerup_ipra_2026-11-15`](../docs/proofs/analysis/bohr_mollerup_ipra_2026-11-15/), [`goldbach_euler_ipra`](../docs/proofs/analytic-number-theory/goldbach_euler_ipra/), [`stirling_ipra`](../docs/proofs/analysis/stirling_ipra/) | By induction on the length: the Pochhammer shift `r P_m(r + 1) = (r + m) P_m(r)`; `∑_{i=1}^{j} 1/(i(i + 1)) = j/(j + 1)`; the Wallis product `∏_{k≤m} (2k)²/((2k − 1)(2k + 1)) = 16^m (m!)⁴/((2m + 1)((2m)!)²)`, with denominators cleared |
| [`DiophantineNumberTheory/Pell`](Lean/IPRADerivations/DiophantineNumberTheory/Pell.lean) | [`pell_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/pell_ipra_2026-11-15/), [`diophantine_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/diophantine_ipra_2026-11-15/) | Brahmagupta's identity; composition of solutions of `x² = D y² + 1` |
| [`DiophantineNumberTheory/Recurrences`](Lean/IPRADerivations/DiophantineNumberTheory/Recurrences.lean) | [`diophantine_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/diophantine_ipra_2026-11-15/), [`pell_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/pell_ipra_2026-11-15/), [`hurwitz_khinchin_ipra`](../docs/proofs/diophantine-number-theory/hurwitz_khinchin_ipra/) | With the index as an iPRA variable: the powers `(x_m, y_m)` of a Pell solution keep `x_m² = D y_m² + 1` and satisfy `x_{m+2} + x_m = 2u x_{m+1}`; for every symbol of partial quotients, the convergent determinant `d_j` has `d_{j+1} = −d_j` and `d_j² = 1`; `(F_{n+1}² − F_{n+1}F_n − F_n²)² = 1` for the Fibonacci numbers |
| [`DiophantineNumberTheory/Siegel`](Lean/IPRADerivations/DiophantineNumberTheory/Siegel.lean) | [`siegel_ipra`](../docs/proofs/diophantine-number-theory/siegel_ipra/), [`ipra_framework`](../docs/proofs/foundations/ipra_framework/) | For every `m ≥ 1`, integral points of `y² = x^{2m} + x + 1` have `x ∈ {0, −1}`, by squeezing `y²` between consecutive squares (both signs of `x`); the power gap `a < b → a^m + a^{m−1} ≤ b^m` |
| [`Combinatorics/Binomial`](Lean/IPRADerivations/Combinatorics/Binomial.lean) | the binomial-coefficient packets (`pnt_ipra_constructive_2026-11-14`, `lagrange_inversion_ipra`, `bell_numbers_ipra`) | `C(n, k) = n! div k!(n − k)!` is exact for `k ≤ n` (one induction on `n`, with the sum `∑_{k≤n} (n! mod k!(n−k)!)` as a bounded quantifier), Pascal's rule, and `C(n, 0) = C(n, n) = 1` |
| [`Combinatorics/BinomialIdentities`](Lean/IPRADerivations/Combinatorics/BinomialIdentities.lean) | [`pnt_ipra_constructive_2026-11-14`](../docs/proofs/analytic-number-theory/pnt_ipra_constructive_2026-11-14/), [`lagrange_inversion_ipra`](../docs/proofs/algebra/lagrange_inversion_ipra/) | `∑_{k≤m} C(m, k) = 2^m`; `C(2n, n) ≤ 2^{2n}`; for `n ≥ 1`, `n C(2n, n) = (n + 1) C(2n, n + 1)` and the Catalan identity `(n + 1)(C(2n, n) − C(2n, n + 1)) = C(2n, n)` |
| [`Combinatorics/BinomialTheorem`](Lean/IPRADerivations/Combinatorics/BinomialTheorem.lean) | [`lagrange_inversion_ipra`](../docs/proofs/algebra/lagrange_inversion_ipra/), [`von_mangoldt_totient_ipra_2026-11-15`](../docs/proofs/analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15/) | The binomial theorem `∑_{k≤m} C(m, k) aᵏ = (a + 1)ᵐ`, with the summand reading `m, a` from the pair `⟨m, a⟩`; pulling a parameter factor out of a bounded sum |
| [`DiophantineNumberTheory/Hurwitz`](Lean/IPRADerivations/DiophantineNumberTheory/Hurwitz.lean) | [`hurwitz_khinchin_ipra`](../docs/proofs/diophantine-number-theory/hurwitz_khinchin_ipra/) | For every symbol of partial quotients `a_j ≥ 1`, the convergent denominators satisfy `q_j ≥ j` |
| [`DiophantineNumberTheory/Coprime`](Lean/IPRADerivations/DiophantineNumberTheory/Coprime.lean) | [`flt_ipra`](../docs/proofs/diophantine-number-theory/flt_ipra/) (`lem:integer-tools`) | Gauss's lemma `gcd(m, a) = 1 → m ∣ ay → m ∣ y`; coprimality passes to divisors and products; coprime factors of a square: `ab = c²`, `gcd(a, b) = 1`, `a ≥ 1` give `a = gcd(a, c)²` (without factorization) |
| [`DiophantineNumberTheory/Identities`](Lean/IPRADerivations/DiophantineNumberTheory/Identities.lean) | [`flt_ipra`](../docs/proofs/diophantine-number-theory/flt_ipra/), [`diophantine_geometry_ipra`](../docs/proofs/diophantine-number-theory/diophantine_geometry_ipra/), [`faltings_ipra`](../docs/proofs/diophantine-number-theory/faltings_ipra/) | `(t + s√5)⁵ = tG + 5sF√5` and its norm `(tG)² − 5(5sF)² = (t² − 5s²)⁵`; the Pythagorean parametrisation; the Pythagorean triangle of `x⁴ − y⁴ = z²` |
| [`Foundations/QuantitativeIdentities`](Lean/IPRADerivations/Foundations/QuantitativeIdentities.lean) | finite-use, contract-compiler and embedding frameworks; `goldbach_euler_ipra`, `zeta_zeros_ipra_2026-11-15`, `gamma_ipra` | The product-contract and cubic-difference identities; `xᵏ − yᵏ = (x − y) ∑ xⁱ y^{k−1−i}` and `xᵏ = (x − 1) ∑ xⁱ + 1` as schemas in `k`; `3 + 4c + (2c² − 1) = 2(1 + c)²`; the rational parametrisation of the circle |
| [`Foundations/Termination`](Lean/IPRADerivations/Foundations/Termination.lean) | [`ipra_unified_finitary_framework_2026-11-15`](../docs/proofs/foundations/ipra_unified_finitary_framework_2026-11-15/) | For all symbols `done`, `step`, `m`: if every non-terminal step decreases `m`, the stopped run from `s₀` is terminal after `m(s₀) + 1` steps |
| [`Foundations/ChineseRemainder`](Lean/IPRADerivations/Foundations/ChineseRemainder.lean) | [`ipra_categorical_methods`](../docs/proofs/foundations/ipra_categorical_methods/) | The two-modulus Chinese remainder theorem without coprimality (`thm:crt`): for `a, b ≥ 1`, residues of `r` mod `a` and `s` mod `b` that agree mod `g = gcd(a, b)` are the residues of the explicit `x = r + a P (β + α (b/g − 1))`, built from Bézout's identity; numbers with equal residues mod `a` and mod `b` have equal residues mod `a (b / g)` |
| [`Geometry/EulerRodrigues`](Lean/IPRADerivations/Geometry/EulerRodrigues.lean) | [`euler_rodrigues_ipra`](../docs/proofs/geometry/euler_rodrigues_ipra/) | For the Euler–Rodrigues matrix `R` of `(a, v)`: `Rᵀ R = (a² + v·v)² I`, `det R = (a² + v·v)³`, `R v = (a² + v·v) v`; for 3×3 matrices, `adj (I − B)`, `det (I − B)` and `adj (adj B) = (det B) B` |
| [`Geometry/Morley`](Lean/IPRADerivations/Geometry/Morley.lean) | [`morley_ipra_constructive`](../docs/proofs/geometry/morley_ipra_constructive/) | The trisector identity `3s − 4s³ = s (ρc + s)(ρc − s)` from `s² + c² = 1` and `ρ² = 3` |
| [`Geometry/PlatonicSolids`](Lean/IPRADerivations/Geometry/PlatonicSolids.lean) | [`platonic_solids_ipra`](../docs/proofs/geometry/platonic_solids_ipra/) | From `V − E + F = 2`, `qV = 2E`, `pF = 2E` and `p, q ≥ 3`: `{p, q}` is one of `{3,3}`, `{3,4}`, `{4,3}`, `{3,5}`, `{5,3}` |
| [`Geometry/Projective`](Lean/IPRADerivations/Geometry/Projective.lean) | [`desargues_pascal_ipra`](../docs/proofs/geometry/desargues_pascal_ipra/), [`eight_geometry_theorems_ipra`](../docs/proofs/geometry/eight_geometry_theorems_ipra/) | The double cross identity, the universal Desargues identity `[XYZ] = [abc][ABC][a×A, b×B, c×C]`, the Plücker relation and the Pappus identity `X − Y + Z = 0` |
| [`Geometry/SphericalTrigonometry`](Lean/IPRADerivations/Geometry/SphericalTrigonometry.lean) | [`spherical_trigonometry_ipra_2026-11-15`](../docs/proofs/geometry/spherical_trigonometry_ipra_2026-11-15/) | Binet–Cauchy, the Gram identity for `[u v w]²`, the Lagrange identity, and the division-free spherical cosine law under `u·u = 1` |
| [`Geometry/TriangleFormulas`](Lean/IPRADerivations/Geometry/TriangleFormulas.lean) | [`triangle_formulas_ipra`](../docs/proofs/geometry/triangle_formulas_ipra/) | two-square identity, Heron factorisation, Heron's formula and the law of cosines in integer coordinates |
| [`Topology/Sperner`](Lean/IPRADerivations/Topology/Sperner.lean) | [`dimension_invariance_ipra`](../docs/proofs/topology/dimension_invariance_ipra/) | The one-dimensional Sperner lemma: for every labelling `ℓ = par ∘ f`, the number of label changes along `0, …, N` has the parity of `ℓ(N) − ℓ(0)`, so it is odd when `ℓ(0) = 0` and `ℓ(N) = 1` |

Some theorems are *schemas*. One Lean theorem then gives an iPRA theorem for
each matrix size `k`, exponent `k` or primitive recursive symbol `f`. Inside each
such iPRA theorem every number variable is a variable of the formula. In the
`Core/Sums` theorems the bound `n` is such a variable, and the derivation uses
the induction axiom of `PRAAx`.

## How the ring tool yields iPRA derivations

Provable equality under `Γ` is a congruence for `+` and `*`, and the semiring
laws are derivable. So the quotient `Q Γ` is a commutative semiring, and
`Q.exact` turns an equality of classes back into a derivation. Integers are
encoded as pairs `(p, q)` standing for `p − q`. The integer equation
`(p, q) = (p', q')` is the quantifier-free formula `p + q' ≐ p' + q`, and
products and sums of pairs are the usual polynomial formulas. Thus an integer
identity such as Heron's formula is a single iPRA equation between explicit
natural-number terms. To derive it, the pairs are evaluated in the ring of
differences of `Q Γ`, where Mathlib's `ring` proves the identity. Cancellation,
derived in iPRA, makes the evaluation injective. Mathlib is used only in the
metatheory, to find and check the derivation. The object-level proof uses only
the axioms `PRAAx`.

For larger identities, such as those of linear algebra, the term operations
(`Mat.det`, `Mat.adj`, `Vec.cross`, …) are shown once to evaluate to Mathlib's
`Matrix.det`, `Matrix.adjugate`, `crossProduct` and so on. An identity is then
proved over an arbitrary commutative ring, for instance by `Matrix.mul_adjugate`,
and read back as an iPRA derivation. This is how a single Lean theorem gives
iPRA theorems for matrices of every size.

## Relation to other iPRA work in the repository

`Computability/DiophantineConsistency` and `Computability/BusyBeaver/Research/PA`
develop iPRA in Foundation's first-order framework (`LO.FirstOrder`, with
`𝗜𝗻𝘁¹` and the language `DiophantineConsistency.PRALanguage`). They target the
consistency equation and Busy Beaver statements, with their own PRA language
and calculus. `DiophantineConsistency`'s `HA*Arithmetic` modules derive semiring
laws in a further calculus, `SetTheory.PA`. None of these is stated in
`ConciseIPRA`'s `Prf PRAAx`, and no bridge between the two systems exists. The
packets of `docs/proofs/` target `Prf PRAAx` and `pra_iff_native`, so this
library builds its arithmetic layer there.
