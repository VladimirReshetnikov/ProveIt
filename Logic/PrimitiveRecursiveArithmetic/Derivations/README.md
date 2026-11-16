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
| [`Core/LinearAlgebra`](Lean/IPRADerivations/Core/LinearAlgebra.lean) | Integer vectors and matrices: finite sums, dot and cross products, matrix products, traces, determinants by Laplace expansion and adjugates by cofactors, each evaluated to the corresponding Mathlib operation; matrix equations as finite conjunctions |

The theorem modules are grouped by the areas of `docs/proofs/`:

| Module | Packet | Theorems |
|---|---|---|
| [`Algebra/CayleyHamilton`](Lean/IPRADerivations/Algebra/CayleyHamilton.lean) | [`cayley_hamilton_ipra`](../docs/proofs/algebra/cayley_hamilton_ipra/) | Cayley–Hamilton for 2×2 and 3×3 integer matrices; `M · adj M = (det M) I` and `det (M N) = det M · det N` as schemas, one theorem for every size; `L(q r) = L(q) L(r)` for quaternions and Euler's four-square identity |
| [`Algebra/PolynomialFormulas`](Lean/IPRADerivations/Algebra/PolynomialFormulas.lean) | [`ipra_polynomial_formulas_abel_ruffini`](../docs/proofs/algebra/ipra_polynomial_formulas_abel_ruffini/), [`three_impossibilities_ipra`](../docs/proofs/algebra/three_impossibilities_ipra/) | The quadratic, Cardano and Ferrari factorisations as implications from the defining relations of the radicals and of `ω`; the triple-angle identity on the unit circle |
| [`DiophantineNumberTheory/Pell`](Lean/IPRADerivations/DiophantineNumberTheory/Pell.lean) | [`pell_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/pell_ipra_2026-11-15/), [`diophantine_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/diophantine_ipra_2026-11-15/) | Brahmagupta's identity; composition of solutions of `x² = D y² + 1` |
| [`DiophantineNumberTheory/Recurrences`](Lean/IPRADerivations/DiophantineNumberTheory/Recurrences.lean) | [`diophantine_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/diophantine_ipra_2026-11-15/), [`pell_ipra_2026-11-15`](../docs/proofs/diophantine-number-theory/pell_ipra_2026-11-15/), [`hurwitz_khinchin_ipra`](../docs/proofs/diophantine-number-theory/hurwitz_khinchin_ipra/) | With the index as an iPRA variable: the powers `(x_m, y_m)` of a Pell solution keep `x_m² = D y_m² + 1` and satisfy `x_{m+2} + x_m = 2u x_{m+1}`; for every symbol of partial quotients, the convergent determinant `d_j` has `d_{j+1} = −d_j` and `d_j² = 1`; `(F_{n+1}² − F_{n+1}F_n − F_n²)² = 1` for the Fibonacci numbers |
| [`DiophantineNumberTheory/Identities`](Lean/IPRADerivations/DiophantineNumberTheory/Identities.lean) | [`flt_ipra`](../docs/proofs/diophantine-number-theory/flt_ipra/), [`diophantine_geometry_ipra`](../docs/proofs/diophantine-number-theory/diophantine_geometry_ipra/), [`faltings_ipra`](../docs/proofs/diophantine-number-theory/faltings_ipra/) | `(t + s√5)⁵ = tG + 5sF√5` and its norm `(tG)² − 5(5sF)² = (t² − 5s²)⁵`; the Pythagorean parametrisation; the Pythagorean triangle of `x⁴ − y⁴ = z²` |
| [`Foundations/QuantitativeIdentities`](Lean/IPRADerivations/Foundations/QuantitativeIdentities.lean) | finite-use, contract-compiler and embedding frameworks; `goldbach_euler_ipra`, `zeta_zeros_ipra_2026-11-15`, `gamma_ipra` | The product-contract and cubic-difference identities; `xᵏ − yᵏ = (x − y) ∑ xⁱ y^{k−1−i}` and `xᵏ = (x − 1) ∑ xⁱ + 1` as schemas in `k`; `3 + 4c + (2c² − 1) = 2(1 + c)²`; the rational parametrisation of the circle |
| [`Geometry/EulerRodrigues`](Lean/IPRADerivations/Geometry/EulerRodrigues.lean) | [`euler_rodrigues_ipra`](../docs/proofs/geometry/euler_rodrigues_ipra/) | For the Euler–Rodrigues matrix `R` of `(a, v)`: `Rᵀ R = (a² + v·v)² I`, `det R = (a² + v·v)³`, `R v = (a² + v·v) v`; for 3×3 matrices, `adj (I − B)`, `det (I − B)` and `adj (adj B) = (det B) B` |
| [`Geometry/Morley`](Lean/IPRADerivations/Geometry/Morley.lean) | [`morley_ipra_constructive`](../docs/proofs/geometry/morley_ipra_constructive/) | The trisector identity `3s − 4s³ = s (ρc + s)(ρc − s)` from `s² + c² = 1` and `ρ² = 3` |
| [`Geometry/Projective`](Lean/IPRADerivations/Geometry/Projective.lean) | [`desargues_pascal_ipra`](../docs/proofs/geometry/desargues_pascal_ipra/), [`eight_geometry_theorems_ipra`](../docs/proofs/geometry/eight_geometry_theorems_ipra/) | The double cross identity, the universal Desargues identity `[XYZ] = [abc][ABC][a×A, b×B, c×C]`, the Plücker relation and the Pappus identity `X − Y + Z = 0` |
| [`Geometry/SphericalTrigonometry`](Lean/IPRADerivations/Geometry/SphericalTrigonometry.lean) | [`spherical_trigonometry_ipra_2026-11-15`](../docs/proofs/geometry/spherical_trigonometry_ipra_2026-11-15/) | Binet–Cauchy, the Gram identity for `[u v w]²`, the Lagrange identity, and the division-free spherical cosine law under `u·u = 1` |
| [`Geometry/TriangleFormulas`](Lean/IPRADerivations/Geometry/TriangleFormulas.lean) | [`triangle_formulas_ipra`](../docs/proofs/geometry/triangle_formulas_ipra/) | two-square identity, Heron factorisation, Heron's formula and the law of cosines in integer coordinates |

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
