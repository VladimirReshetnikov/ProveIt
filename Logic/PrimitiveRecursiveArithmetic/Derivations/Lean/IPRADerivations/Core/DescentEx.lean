import IPRADerivations.Core.Descent

/-!
# Infinite descent with an existential step

The descent of `Core.Descent`, except that a solution with `b ≠ 0` need only yield *some*
smaller solution: `∃ a' b'. χ(a', b') = 1 ∧ b' < b`. Steps that branch into cases with
different witnesses (as in Fermat's descent for `x⁴ + y⁴ = z²`) are then proofs, not PR
terms. The counting argument is unchanged: the induction formula `T(N) = 0` is
quantifier-free, and the existential is eliminated inside the proof that a counted term
vanishes.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DescentEx

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Descent (T count_zero_of_term_zero no_solution_below)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable (χ : PTm 2) (β : PTm 1)

/-- The hypotheses, over the variables `0 = a`, `1 = b`; under the two quantifiers of
`hstep`, `0 = b'`, `1 = a'`, `2 = a`, `3 = b`. -/
structure Hyps : Prop where
  h01 : ([] : List (Fm PTm 2)) ⊢[PRAAx] (inst2 χ (var 0) (var 1) ≐ zero) ⋎ (inst2 χ (var 0) (var 1) ≐ one)
  h0 : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst2 χ (var 0) zero ≐ zero
  hb : ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] lt (var 0) (inst1 β (var 1))
  hstep : ([var 1 ≐ succ (pred (var 1)), inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
    Fm.ex (Fm.ex ((inst2 χ (var 1) (var 0) ≐ one) ⋏ lt (var 0) (var 3)))

variable {χ β}

theorem bound (H : Hyps χ β) {n : ℕ} {Δ : List (Fm PTm n)} {a b : PTm n}
    (h : Δ ⊢[PRAAx] inst2 χ a b ≐ one) : Δ ⊢[PRAAx] lt a (inst1 β b) := by
  have i := inst (Γ := Δ) (.impI H.hb) ![a, b]
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst1, subst_inst2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at i
  exact .impE i h

/-- In the context `T(b) = 0`: `χ(a, b) = 0`. -/
private theorem term_zero (H : Hyps χ β) :
    ([T χ β (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] inst2 χ (var 0) (var 1) ≐ zero := by
  refine .orE (H.h01.ofNil) Prf.hyp0 ?_
  refine .orE (zero_or_succ (var 1)) ?_ ?_
  · refine .botE _ (succ_ne_zero (a := zero) ?_)
    refine Prf.hyp1.eqSymm.eqTrans ?_
    exact (congrInst2 χ (.eqRefl _) Prf.hyp0).eqTrans H.h0.ofNil
  · refine .botE _ ?_
    have hs := H.hstep.trans (Δ := [var 1 ≐ succ (pred (var 1)), inst2 χ (var 0) (var 1) ≐ one,
      T χ β (var 1) ≐ zero]) (by
        intro ψ hψ; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hψ
        rcases hψ with rfl | rfl
        · exact Prf.hyp0
        · exact Prf.hyp1)
    refine Prf.exE hs (Prf.exE Prf.hyp0 ?_)
    have hT : (((inst2 χ (var 1) (var 0) ≐ one) ⋏ lt (var 0) (var 3)) ::
        (List.map Fm.shift ((Fm.ex ((inst2 χ (var 1) (var 0) ≐ one) ⋏ lt (var 0) (var 3)) : Fm PTm 3) ::
          List.map Fm.shift ([var 1 ≐ succ (pred (var 1)), inst2 χ (var 0) (var 1) ≐ one,
            T χ β (var 1) ≐ zero] : List (Fm PTm 2))))) ⊢[PRAAx] T χ β (var 3) ≐ zero := by
      apply Prf.hyp
      simp [Fm.shift, Syn.shift]
    exact .botE _ (no_solution_below hT (Prf.andE₂ Prf.hyp0) (Prf.andE₁ Prf.hyp0)
      (bound H (Prf.andE₁ Prf.hyp0)))

/-- `T(N) = 0` for every `N`. -/
theorem count_zero (H : Hyps χ β) : ([] : List (Fm PTm 1)) ⊢[PRAAx] T χ β (var 0) ≐ zero :=
  count_zero_of_term_zero (term_zero H)

/-- Infinite descent: `χ(a, b) = 1` is refutable. -/
theorem descent (H : Hyps χ β) :
    ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] Fm.bot := by
  have hT : ([inst2 χ (var 0) (var 1) ≐ one] : List (Fm PTm 2)) ⊢[PRAAx]
      T χ β (succ (var 1)) ≐ zero := by
    simpa using inst (Γ := [inst2 χ (var 0) (var 1) ≐ one]) (count_zero H)
      (![succ (var 1)] : Fin 1 → PTm 2)
  exact no_solution_below hT ((succ_monus_succ _ _).eqTrans (le_refl _)) Prf.hyp0 H.hb

end LeanProofs.IPRA.DescentEx
