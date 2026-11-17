import IPRADerivations.Foundations.BoundedFormulas

/-!
# Booleanization, least bounded search and the least-success invariant

Corollaries of the bounded-formula compiler (`Foundations/BoundedFormulas`) and the least search
(`Core/Search`) in the forms stated by three framework packets:

* `ipra_finitary_interface_compiler_2026-11-15`, `thm:booleanization`, and
  `ipra_staged_contract_kernel_2026-11-15`, `thm:booleanization`: for every bounded formula `B` the
  bit `χ_B` satisfies `χ_B = 1 ↔ B` (`bit_one_iff`) and `χ_B = 0 ↔ ¬B` (`bit_zero_iff`), hence
  `B ∨ ¬B`; implication is the derived connective `imp A B = ¬A ∨ B`, with
  `imp A B ↔ (A → B)` (`imp_iff`), using decidability of `A`;
* `ipra_staged_contract_kernel_2026-11-15`, `thm:least-search`: `∃ i < B P(i)` gives
  `P(least) ∧ least < B ∧ ∀ j < least ¬P(j)` (`least_spec`), and failure `least = B` is
  equivalent to `∀ i < B ¬P(i)` (`least_none_of`, `none_of_least`);
* `ipra_cbip_framework_2026-11-16`, `lem:first`: for a Boolean-valued body `f`,
  `first(b) ≤ b`, `first(b) < b → f(first(b)) = 1`, `j < first(b) → f(j) = 0` (`first_le`,
  `first_found`, `first_before`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BooleanizationCorollaries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedFormulas
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {m : ℕ} {Δ : List (Fm PTm m)}

/-! ## Booleanization -/

theorem bit_one_iff (A : BF) (y : PTm m) : Δ ⊢[PRAAx] Fm.iff (bitAt A m y ≐ one) (fmAt A m y) :=
  Prf.iffI (reflect A y).2.1 (reflect A y).1

theorem bit_zero_of_neg (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] neg (fmAt A m y)) : Δ ⊢[PRAAx] bitAt A m y ≐ zero :=
  .orE (bf_cases A y) Prf.hyp0 (.botE _ (.impE h.wk (.impE (reflect A y).2.1 Prf.hyp0)))

theorem neg_of_bit_zero (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] bitAt A m y ≐ zero) : Δ ⊢[PRAAx] neg (fmAt A m y) :=
  .impI (clash _ h.wk (.impE (reflect A y).1 Prf.hyp0))

/-- `χ_B = 0 ↔ ¬B`. -/
theorem bit_zero_iff (A : BF) (y : PTm m) : Δ ⊢[PRAAx] Fm.iff (bitAt A m y ≐ zero) (neg (fmAt A m y)) :=
  Prf.iffI (.impI (neg_of_bit_zero A Prf.hyp0)) (.impI (bit_zero_of_neg A Prf.hyp0))

/-- Implication as a derived bounded connective. -/
def imp (A B : BF) : BF := .or (.not A) B

theorem imp_iff (A B : BF) (y : PTm m) :
    Δ ⊢[PRAAx] Fm.iff (fmAt (imp A B) m y) (fmAt A m y ⟶ fmAt B m y) := by
  refine Prf.iffI (.impI (.impI ?_)) (.impI ?_)
  · exact .orE (show _ ⊢[PRAAx] fmAt (.not A) m y ⋎ fmAt B m y from Prf.hyp1)
      (.botE _ (.impE Prf.hyp0 Prf.hyp1)) Prf.hyp0
  · exact .orE (bf_dec A y) (.orI₂ (.impE Prf.hyp1 Prf.hyp0)) (.orI₁ Prf.hyp0)

/-! ## Least bounded search -/

section Least

variable (B : PTm 1) (P : BF)

theorem shift_bfWit (x : PTm m) : Syn.shift (bfWit B P x) = bfWit B P (Syn.shift x) := by
  simp only [bfWit, Syn.shift, BoundedReflection.wit, subst_ap2, at1_subst]

/-- `thm:least-search`: the least witness of `∃ i < B P(i)`. -/
theorem least_spec {x : PTm m} (h : Δ ⊢[PRAAx] fmAt (.ex B P) m x) :
    Δ ⊢[PRAAx] fmAt P m (pairT (bfWit B P x) x) ⋏ (lt (bfWit B P x) (at1 B x) ⋏
      Fm.all (lt (var 0) (Syn.shift (bfWit B P x)) ⟶ neg (fmAt P (m + 1) (pairT (var 0) (Syn.shift x))))) := by
  have c := bf_choice B P x h
  refine .andI (Prf.andE₂ c) (.andI (Prf.andE₁ c) (.allI (.impI ?_)))
  rw [shift_bfWit]
  exact bf_least B P (Syn.shift x) (var 0) Prf.hyp0

/-- `thm:least-search`, failure: if no index below `B` satisfies `P`, the search returns `B`. -/
theorem least_none_of {x : PTm m}
    (h : Δ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (at1 B x)) ⟶ neg (fmAt P (m + 1) (pairT (var 0) (Syn.shift x))))) :
    Δ ⊢[PRAAx] bfWit B P x ≐ at1 B x := by
  have s := Search.search_spec (Γ := Δ) (f := BoundedReflection.nB (body P)) (at1 B x) zero x
  refine .orE (lt_or_le (bfWit B P x) (at1 B x)) ?_ (le_antisymm (Prf.andE₁ s).wk Prf.hyp0)
  have z := Prf.impE (Prf.andE₁ (Prf.andE₂ s)).wk Prf.hyp0
  rw [BoundedReflection.inst2_nB, inst2_body] at z
  have one : (lt (bfWit B P x) (at1 B x) :: Δ) ⊢[PRAAx] bitAt P m (pairT (bfWit B P x) x) ≐ one :=
    .orE (bf_cases P _) (.botE _ (BoundedReflection.one_ne_zero _
      ((monus_zero one).eqSymm.eqTrans ((congrMonus (.eqRefl one) Prf.hyp0.eqSymm).eqTrans z.wk)))) Prf.hyp0
  have i := Prf.allE (bfWit B P x) (h.wk (ψ := lt (bfWit B P x) (at1 B x)))
  simp only [Fm.subst_imp, subst_lt, subst_neg, Syn.subst_var, Syn.inst_zero, fmAt_subst, subst_pairT, Syn.subst_shift,
    Syn.inst, Fin.cases_succ, Syn.subst_id] at i
  exact .botE _ (.impE (.impE i Prf.hyp0) (.impE (reflect P _).2.1 one))

/-- `thm:least-search`, failure: if the search returns `B`, no index below `B` satisfies `P`. -/
theorem none_of_least {x : PTm m} (h : Δ ⊢[PRAAx] bfWit B P x ≐ at1 B x) :
    Δ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (at1 B x)) ⟶ neg (fmAt P (m + 1) (pairT (var 0) (Syn.shift x)))) := by
  refine .allI (.impI ?_)
  have h' : (Δ.map Fm.shift) ⊢[PRAAx] bfWit B P (Syn.shift x) ≐ Syn.shift (at1 B x) := by
    have := h.shift
    simp only [Fm.shift, Fm.subst_eq] at this
    rw [← shift_bfWit]; exact this
  exact bf_least B P (Syn.shift x) (var 0) (lt_congr (.eqRefl _) h'.wk.eqSymm Prf.hyp0)

end Least

/-! ## The least-success invariant for a Boolean predicate -/

section First

variable (f : PTm 2)

/-- `1 ∸ f`. -/
abbrev nf : PTm 2 := monus one f

/-- `first(b, f)`: the least `i < b` with `f(i) = 1`, or `b`. -/
abbrev first (b x : PTm m) : PTm m := Search.mu (nf f) b x

theorem inst2_nf (i x : PTm m) : inst2 (nf f) i x = monus one (inst2 f i x) := by simp [inst2]

theorem first_le (b x : PTm m) : Δ ⊢[PRAAx] le (first f b x) b := Prf.andE₁ (Search.search_spec _ zero x)

/-- `first(b) < b → f(first(b)) = 1`, for a Boolean value at `first(b)`. -/
theorem first_found {b x : PTm m} (hb : Δ ⊢[PRAAx] (inst2 f (first f b x) x ≐ zero) ⋎ (inst2 f (first f b x) x ≐ one))
    (h : Δ ⊢[PRAAx] lt (first f b x) b) : Δ ⊢[PRAAx] inst2 f (first f b x) x ≐ one := by
  have z := Prf.impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec (Γ := Δ) (f := nf f) b zero x))) h
  rw [inst2_nf] at z
  exact .orE hb (BoundedReflection.one_ne_zero _ ((monus_zero one).eqSymm.eqTrans
    ((congrMonus (.eqRefl one) Prf.hyp0.eqSymm).eqTrans z.wk))) Prf.hyp0

/-- `j < first(b) → f(j) = 0`, for a Boolean value at `j`. -/
theorem first_before {b j x : PTm m} (hb : Δ ⊢[PRAAx] (inst2 f j x ≐ zero) ⋎ (inst2 f j x ≐ one))
    (h : Δ ⊢[PRAAx] lt j (first f b x)) : Δ ⊢[PRAAx] inst2 f j x ≐ zero := by
  have z := Search.search_minimal (f := nf f) h
  rw [inst2_nf] at z
  exact .orE hb Prf.hyp0 (.botE _ (.impE z.wk ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one))))

end First

end LeanProofs.IPRA.Foundations.BooleanizationCorollaries
