import PA194ForwardFormulaQuoteSteps
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ForwardTyped
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formula_quote {n : Nat} (p : SourceFormula n) : ∀ {m : Nat} (b : Fin n → Term m)
    (f : Nat → Term m) (z : Term m) (param : V), Aligned param b f z →
    (⌜p⌝ : V) < len (nth param 1) → translateFormula param (⌜p⌝ : V) = ⌜formula p b f⌝ := by
  induction p with
  | verum =>
    intro m b f z param h hlen
    change translateFormula param (^⊤ : V) = (^⊤ : V)
    exact translate_verum param
  | falsum =>
    intro m b f z param h hlen
    change translateFormula param (^⊥ : V) = (^⊥ : V)
    exact translate_falsum param
  | rel r ts =>
    cases r with
    | eq =>
      intro m b f z param h hlen
      have hr : PA194PAeq.language.IsRel (2 : V) 0 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by
        simp [quote_term_valid]
      rw [quote_eq_rel] at hlen ⊢
      have ha : (⌜ts 0⌝ : V) < len (nth param 1) := lt_trans (by simpa using
        (nth_lt_qqRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[⌜ts 0⌝,⌜ts 1⌝] : V)) (i := (0 : V)) (by simp))) hlen
      have hc : (⌜ts 1⌝ : V) < len (nth param 1) := lt_trans (by simpa using
        (nth_lt_qqRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[⌜ts 0⌝,⌜ts 1⌝] : V)) (i := (1 : V)) (by simp))) hlen
      rw [translate_rel param _ _ _ hr hv]
      simpa [formula] using atomicEquality_quote (ts 0) (ts 1) b f z param h ha hc
  | nrel r ts =>
    cases r with
    | eq =>
      intro m b f z param h hlen
      have hr : PA194PAeq.language.IsRel (2 : V) 0 := by simp
      have hv : IsUTermVec PA194PAeq.language (2 : V) (?[⌜ts 0⌝,⌜ts 1⌝] : V) := by
        simp [quote_term_valid]
      rw [quote_eq_nrel] at hlen ⊢
      have ha : (⌜ts 0⌝ : V) < len (nth param 1) := lt_trans (by simpa using
        (nth_lt_qqNRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[⌜ts 0⌝,⌜ts 1⌝] : V)) (i := (0 : V)) (by simp))) hlen
      have hc : (⌜ts 1⌝ : V) < len (nth param 1) := lt_trans (by simpa using
        (nth_lt_qqNRel_of_lt (k := (2 : V)) (r := (0 : V)) (v := (?[⌜ts 0⌝,⌜ts 1⌝] : V)) (i := (1 : V)) (by simp))) hlen
      rw [translate_nrel param _ _ _ hr hv]
      have hv1 : nth (?[⌜ts 0⌝,⌜ts 1⌝] : V) 1 = (⌜ts 1⌝ : V) := by simp
      simp only [nth_adjoin_zero,hv1]
      change neg SourceL (atomicEquality param (⌜ts 0⌝ : V) ⌜ts 1⌝) = (⌜∼equal (ts 0) (ts 1) b f⌝ : V)
      rw [quote_neg,atomicEquality_quote (ts 0) (ts 1) b f z param h ha hc]
  | and p q ihp ihq =>
    intro m b f z param h hlen
    have hp : IsUFormula PA194PAeq.language (⌜p⌝ : V) := (Semiformula.quote_isSemiformula p).isUFormula
    have hq : IsUFormula PA194PAeq.language (⌜q⌝ : V) := (Semiformula.quote_isSemiformula q).isUFormula
    change ((⌜p⌝ : V) ^⋏ (⌜q⌝ : V)) < len (nth param 1) at hlen
    change translateFormula param ((⌜p⌝ : V) ^⋏ (⌜q⌝ : V)) = _
    have hp' : (⌜p⌝ : V) < (⌜p⌝ : V) ^⋏ (⌜q⌝ : V) := by
      change (⌜p⌝ : V) < pair (4 : V) (pair (⌜p⌝ : V) (⌜q⌝ : V)) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_left _ _) (le_pair_right _ _)) (lt_add_one _)
    have hq' : (⌜q⌝ : V) < (⌜p⌝ : V) ^⋏ (⌜q⌝ : V) := by
      change (⌜q⌝ : V) < pair (4 : V) (pair (⌜p⌝ : V) (⌜q⌝ : V)) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_pair_right _ _)) (lt_add_one _)
    rw [translate_and param _ _ hp hq,ihp b f z param h (lt_trans hp' hlen),ihq b f z param h (lt_trans hq' hlen)]
    rfl
  | or p q ihp ihq =>
    intro m b f z param h hlen
    have hp : IsUFormula PA194PAeq.language (⌜p⌝ : V) := (Semiformula.quote_isSemiformula p).isUFormula
    have hq : IsUFormula PA194PAeq.language (⌜q⌝ : V) := (Semiformula.quote_isSemiformula q).isUFormula
    change ((⌜p⌝ : V) ^⋎ (⌜q⌝ : V)) < len (nth param 1) at hlen
    change translateFormula param ((⌜p⌝ : V) ^⋎ (⌜q⌝ : V)) = _
    have hp' : (⌜p⌝ : V) < (⌜p⌝ : V) ^⋎ (⌜q⌝ : V) := by
      change (⌜p⌝ : V) < pair (5 : V) (pair (⌜p⌝ : V) (⌜q⌝ : V)) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_left _ _) (le_pair_right _ _)) (lt_add_one _)
    have hq' : (⌜q⌝ : V) < (⌜p⌝ : V) ^⋎ (⌜q⌝ : V) := by
      change (⌜q⌝ : V) < pair (5 : V) (pair (⌜p⌝ : V) (⌜q⌝ : V)) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_pair_right _ _)) (lt_add_one _)
    rw [translate_or param _ _ hp hq,ihp b f z param h (lt_trans hp' hlen),ihq b f z param h (lt_trans hq' hlen)]
    rfl
  | all p ih =>
    intro m b f z param h hlen
    have hp : IsUFormula PA194PAeq.language (⌜p⌝ : V) := (Semiformula.quote_isSemiformula p).isUFormula
    change (^∀ (⌜p⌝ : V)) < len (nth param 1) at hlen
    change translateFormula param (^∀ (⌜p⌝ : V)) = _
    have hp' : (⌜p⌝ : V) < ^∀ (⌜p⌝ : V) := by
      change (⌜p⌝ : V) < pair (6 : V) (⌜p⌝ : V) + 1
      exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)
    have hl : (⌜p⌝ : V) < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length h.1.2.1] using lt_trans hp' hlen
    rw [translate_all param _ hp,ih (bindEnv b) (shiftEnv f) (Rew.bShift z) (formulaChildParameters param) (aligned_formulaChild h) hl,allOutput_quote]
    rfl
  | exs p ih =>
    intro m b f z param h hlen
    have hp : IsUFormula PA194PAeq.language (⌜p⌝ : V) := (Semiformula.quote_isSemiformula p).isUFormula
    change (^∃ (⌜p⌝ : V)) < len (nth param 1) at hlen
    change translateFormula param (^∃ (⌜p⌝ : V)) = _
    have hp' : (⌜p⌝ : V) < ^∃ (⌜p⌝ : V) := by
      change (⌜p⌝ : V) < pair (7 : V) (⌜p⌝ : V) + 1
      exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)
    have hl : (⌜p⌝ : V) < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length h.1.2.1] using lt_trans hp' hlen
    rw [translate_exs param _ hp,ih (bindEnv b) (shiftEnv f) (Rew.bShift z) (formulaChildParameters param) (aligned_formulaChild h) hl,exsOutput_quote]
    rfl
#print axioms formula_quote
end generic
end PA194ForwardTyped
