# Lean formalization interface (design, not checked Lean code)

Target pinned version: leanprover/lean4:v4.35.0; Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679 (as stated in upstream README).

## Reuse the actual analytic lemma

Module: `Lib.Analytic.Landau.PolarLandau`.
`IsPolar.landau` takes `h : IsPolar E r`, `0 < β`, real-residue
nonnegativity for `β < x`, an eventual `E v ≤ exp ((β-1)*v)` bound,
and `β < ρ.re`; concludes `r ρ = 0`.

Implement Dedekind logarithmic derivative and prime ideal power sum.
Define `R_E x` with Euler–Kronecker constant `-1-γ_E` (prove this
matches the convergent centered integral), and `Φ_E s` from equation (3.2)
of the report, i.e. `(B_E s / s - 1/(s-1) - κ_E)/(s-1)`.
Prove `IsPolar (fun v => R_E (exp v)) r_E` with `r_E` the actual
residue, set to zero at regular points. At positive real part and `s ≠ 1`,
use logarithmic derivative of a meromorphic function with known order.
At 1 prove removability using the Laurent expansion. Check measurable
and growth conditions, and analytic continuation on `Re s ≥ 1`.
For positive weights prove finite sums preserve these properties and
residue formula. Normalize the upper bound by a strictly positive C;
apply `IsPolar.landau`, multiply back by C and use nonnegative integer
zero orders and positive weights. Use full prime powers to meet the global
meromorphic hypothesis; prove prime-only tail comparison separately.

## Independent finite group layer

1. Define virtual character `Θ : G → ℂ` using orders of meromorphic Artin
   functions; represent its restriction to any monomial subgroup by a
   unitary representation of dimension `m`. This requires Hecke holomorphy
   and Artin induction/restriction formalism, not Artin holomorphy.
2. Define `a t = (m + re (Θ t))/2`; identify with the fixed-subfield zero order.
3. Define the exceptional eigenspace dimension for each involution `u`.
   Prove codimension of an intersection is at most the sum of codimensions;
   for commuting reflections the intersection of -1 eigenspaces lies in
   the scalar determinant eigenspace of the product.
4. Prove a product of two involutions generates a cyclic or dihedral group;
   all its irreducibles are linear or induced from a cyclic subgroup.
   In its determinant-twisted representation, intersection of fixed spaces
   is fixed by the product. Bound trace deficit by twice the codimension.
5. Use `∑ g, det g * Θ g = 0` from Dirichlet nonvanishing and character
   orthogonality. Average the pointwise trace deficits.
6. For permutations construct reversals `i ↦ -i`, `i ↦ 1-i` on each cycle;
   prove they compose to the cycle and count disjoint 2-cycles. Prove the
   average cycle count by the insertion bijection. For Coxeter groups add
   the length-additive two-involution factorization separately.
7. Identify fixed coset count with degree-one prime ideals by unramified
   decomposition theory; prove the ramified and higher-power error.

The report proves the mathematical reductions using classical inputs.
This interface does not pretend the new Dedekind, Artin, or character
infrastructure already exists in the pinned Mathlib or the upstream repo.
No local Lean executable was available; no generated Lean theorem is claimed.
