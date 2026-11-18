import IPRADerivations.Foundations.BooleanBits
import IPRADerivations.Foundations.IterationFusion

/-!
# Guarded totalization

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`,
`ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`, Theorem `thm:totalization` ("Guarded
totalization"): a partial operation whose correctness proof uses a decidable guard is made a total primitive
recursive program by returning a fixed default when the guard checker fails; iPRA proves the output contract
under the guard, and no claim is made when the guard fails.

For a guard bit `g`, a computed value `a` and a default `d`, the total program is the selector
`sel g a d = g · a + (1 ∸ g) · d`.

* `sel_one`, `sel_zero`: `g = 1` gives `sel g a d = a`; `g = 0` gives `sel g a d = d`;
* `sel_cases`: for a proved bit `g`, `sel g a d = a ∨ sel g a d = d`;
* `totalization`: for an arbitrary output contract `V(y, x)`, `g = 1 → V(a, x) → V(sel g a d, x)`;
* `totalization_guarded`: if the partial program is correct under the guard, `g = 1 → V(a, x)`, then so is
  the total one, `g = 1 → V(sel g a d, x)`.
-/

namespace LeanProofs.IPRA.Foundations.GuardedTotalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedFormulas (not_of_zero not_of_one)
open LeanProofs.IPRA.Foundations.BooleanBits (Bit)
open LeanProofs.IPRA.Foundations.IterationFusion (rel rel_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The total program: the value under the guard, the default otherwise. -/
abbrev sel (g a d : PTm n) : PTm n := g * a + monus one g * d

section Selector

variable {g a d : PTm n}

theorem sel_one (h : Γ ⊢[PRAAx] g ≐ one) : Γ ⊢[PRAAx] sel g a d ≐ a := by
  have e := natEq h
  have e₂ := natEq (not_of_one h)
  apply deriveNat; ipra_simps
  rw [e, e₂]; ring

theorem sel_zero (h : Γ ⊢[PRAAx] g ≐ zero) : Γ ⊢[PRAAx] sel g a d ≐ d := by
  have e := natEq h
  have e₂ := natEq (not_of_zero h)
  apply deriveNat; ipra_simps
  rw [e, e₂]; ring

theorem sel_cases (hg : Γ ⊢[PRAAx] Bit g) : Γ ⊢[PRAAx] (sel g a d ≐ a) ⋎ (sel g a d ≐ d) :=
  .orE hg (.orI₂ (sel_zero Prf.hyp0)) (.orI₁ (sel_one Prf.hyp0))

end Selector

/-- `thm:totalization`: under the guard, the total program inherits the output contract of the value. -/
theorem totalization (V : Fm PTm 2) (g a d x : PTm n) :
    Γ ⊢[PRAAx] (g ≐ one) ⟶ (rel V a x ⟶ rel V (sel g a d) x) := by
  refine .impI (.impI ?_)
  have hg : (rel V a x :: (g ≐ one) :: Γ) ⊢[PRAAx] g ≐ one := Prf.hyp1
  exact rel_congr V (sel_one hg).eqSymm (.eqRefl x) Prf.hyp0

/-- If the partial program is correct under the guard, so is the total one. -/
theorem totalization_guarded {V : Fm PTm 2} {g a d x : PTm n}
    (h : Γ ⊢[PRAAx] (g ≐ one) ⟶ rel V a x) : Γ ⊢[PRAAx] (g ≐ one) ⟶ rel V (sel g a d) x := by
  refine .impI ?_
  have hg : ((g ≐ one) :: Γ) ⊢[PRAAx] g ≐ one := Prf.hyp0
  exact Prf.impE (Prf.impE (totalization V g a d x) hg) (Prf.impE h.wk hg)

end LeanProofs.IPRA.Foundations.GuardedTotalization
