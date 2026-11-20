import IPRADerivations.Algebra.BringLipschitz

/-!
# The fourth-order differential resolvent of the Bring quintic

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:differential-resolvent` (Cockle–Harley): every simple
branch of `t − t⁵ = ρ` satisfies
`(256 − 3125ρ⁴)/1155 · t⁽⁴⁾ − 6250ρ³/231 · t''' − 4875ρ²/77 · t'' − 2125ρ/77 · t' + t = 0`.
"Substitute the four rational derivative expressions into the left side, multiply by `1155 D⁷`, and replace `ρ` by
`t − t⁵` ... Polynomial normalization gives zero. ... In iPRA, the same calculation is an integer ring identity
under the guarded hypothesis `D ≠ 0`."

With `D = 1 − 5t⁴` (so `dt/dρ = 1/D`), the derivatives are `t⁽ᵏ⁾ = N_k/D^{2k−1}`, where
`N_{k+1} = N_k' D − (2k − 1) N_k D'` (formal derivatives in `t`), `N_1 = 1`:

* `deriv_numerators`: `N_2 = 20t³`, `N_3 = 900t⁶ + 60t²`, `N_4 = 63000t⁹ + 10800t⁵ + 120t` satisfy the recursion
  with the explicit formal derivatives `D' = −20t³`, `N_2' = 60t²`, `N_3' = 5400t⁵ + 120t`;
* `cockle_harley`: the cleared resolvent identity
  `(256 − 3125ρ⁴) N_4 − 31250ρ³ N_3 D² − 73125ρ² N_2 D⁴ − 31875ρ N_1 D⁶ + 1155 t D⁷ = 0` for `ρ = t − t⁵`,
  an identity of integer terms in `t`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.BringDifferential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

section
variable (t : ZT n)
/-- `t^k`. -/
abbrev P2 : ZT n := t * t
abbrev P3 : ZT n := t * t * t
abbrev P4 : ZT n := t * t * t * t
/-- `D = 1 − 5t⁴`. -/
abbrev DD : ZT n := ZT.natLit 1 - ZT.natLit 5 * P4 t
/-- `ρ = t − t⁵`. -/
abbrev RHO : ZT n := t - P4 t * t
/-- `N_2 = 20t³`. -/
abbrev N2 : ZT n := ZT.natLit 20 * P3 t
/-- `N_3 = 900t⁶ + 60t²`. -/
abbrev N3 : ZT n := ZT.natLit 900 * (P3 t * P3 t) + ZT.natLit 60 * P2 t
/-- `N_4 = 63000t⁹ + 10800t⁵ + 120t`. -/
abbrev N4 : ZT n := ZT.natLit 63000 * (P3 t * P3 t * P3 t) + ZT.natLit 10800 * (P4 t * t) + ZT.natLit 120 * t
end

/-- The recursion `N_{k+1} = N_k' D − (2k − 1) N_k D'` with explicit formal derivatives. -/
theorem deriv_numerators (t : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (N2 t) (ZT.natLit 0 * DD t - ZT.natLit 1 * ZT.natLit 1 * (-(ZT.natLit 20 * P3 t)))) ∧
    (Γ ⊢[PRAAx] ZT.eq (N3 t) (ZT.natLit 60 * P2 t * DD t - ZT.natLit 3 * N2 t * (-(ZT.natLit 20 * P3 t)))) ∧
    (Γ ⊢[PRAAx] ZT.eq (N4 t) ((ZT.natLit 5400 * (P4 t * t) + ZT.natLit 120 * t) * DD t -
      ZT.natLit 5 * N3 t * (-(ZT.natLit 20 * P3 t)))) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_, ZT.derive ?_⟩ <;>
    (simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]; push_cast; ring)

/-- `thm:differential-resolvent`, cleared by `1155 D⁷` with `ρ = t − t⁵`. -/
theorem cockle_harley (t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 256 - ZT.natLit 3125 * (RHO t * RHO t * RHO t * RHO t)) * N4 t -
      ZT.natLit 31250 * (RHO t * RHO t * RHO t) * N3 t * (DD t * DD t) -
      ZT.natLit 73125 * (RHO t * RHO t) * N2 t * (DD t * DD t * DD t * DD t) -
      ZT.natLit 31875 * RHO t * (DD t * DD t * DD t * DD t * DD t * DD t) +
      ZT.natLit 1155 * t * (DD t * DD t * DD t * DD t * DD t * DD t * DD t)) (ZT.natLit 0) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]
  push_cast
  ring

end LeanProofs.IPRA.Algebra.BringDifferential
