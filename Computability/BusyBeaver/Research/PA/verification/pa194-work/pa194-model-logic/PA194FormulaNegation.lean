import PA194FormulaScope
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def NegationProperty (p : V) : Prop :=
  ∀ s n param, IsSemiformula PA194PAeq.language s p → ParametersValid s n param →
    p < len (nth param 1) → neg PA194PAeq.language p < len (nth param 1) →
    translateFormula param (neg PA194PAeq.language p) = neg SourceL (translateFormula param p)
theorem NegationProperty_definable : 𝚷₁-Predicate (NegationProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold NegationProperty ParametersValid
  definability

theorem code_left_lt_and (p q : V) : p < p ^⋏ q := by
  change p < pair (4 : V) (pair p q) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_left _ _) (le_pair_right _ _)) (lt_add_one _)
theorem code_right_lt_and (p q : V) : q < p ^⋏ q := by
  change q < pair (4 : V) (pair p q) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_pair_right _ _)) (lt_add_one _)
theorem code_left_lt_or (p q : V) : p < p ^⋎ q := by
  change p < pair (5 : V) (pair p q) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_left _ _) (le_pair_right _ _)) (lt_add_one _)
theorem code_right_lt_or (p q : V) : q < p ^⋎ q := by
  change q < pair (5 : V) (pair p q) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_pair_right _ _)) (lt_add_one _)
theorem code_lt_all (p : V) : p < ^∀ p := by
  change p < pair (6 : V) p + 1
  exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)
theorem code_lt_exs (p : V) : p < ^∃ p := by
  change p < pair (7 : V) p + 1
  exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)

theorem translateFormula_neg {p : V} (hp : IsUFormula PA194PAeq.language p) : NegationProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction NegationProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv s n param hscope hparam hlen hnlen
    rw [neg_rel hr hv,translate_nrel param k r v hr hv,translate_rel param k r v hr hv]
  · intro k r v hr hv s n param hscope hparam hlen hnlen
    have hpos : IsSemiformula PA194PAeq.language s (^rel k r v) := by
      simpa [IsSemiformula.rel,IsSemiformula.nrel] using hscope
    have hnlen' : (^rel k r v) < len (nth param 1) := by simpa [hr,hv] using hnlen
    have hout := formula_scope_translate hpos.isUFormula s n param hpos hparam hnlen'
    rw [translate_rel param k r v hr hv] at hout
    rw [neg_nrel hr hv,translate_rel param k r v hr hv,translate_nrel param k r v hr hv]
    exact hout.isUFormula.neg_neg.symm
  · intro s n param hscope hparam hlen hnlen
    simp [translate_verum,translate_falsum]
  · intro s n param hscope hparam hlen hnlen
    simp [translate_verum,translate_falsum]
  · intro a b ha hb iha ihb s n param hscope hparam hlen hnlen
    have hs := (IsSemiformula.and).mp hscope
    have hla : a < len (nth param 1) := lt_trans (code_left_lt_and a b) hlen
    have hlb : b < len (nth param 1) := lt_trans (code_right_lt_and a b) hlen
    have hn : neg PA194PAeq.language a ^⋎ neg PA194PAeq.language b < len (nth param 1) := by simpa [ha,hb] using hnlen
    have hna : neg PA194PAeq.language a < len (nth param 1) := lt_trans (code_left_lt_or _ _) hn
    have hnb : neg PA194PAeq.language b < len (nth param 1) := lt_trans (code_right_lt_or _ _) hn
    have hta := (formula_scope_translate ha s n param hs.1 hparam hla).isUFormula
    have htb := (formula_scope_translate hb s n param hs.2 hparam hlb).isUFormula
    rw [neg_and ha hb,translate_or param _ _ ha.neg hb.neg,
      translate_and param a b ha hb,iha s n param hs.1 hparam hla hna,ihb s n param hs.2 hparam hlb hnb,neg_and hta htb]
  · intro a b ha hb iha ihb s n param hscope hparam hlen hnlen
    have hs := (IsSemiformula.or).mp hscope
    have hla : a < len (nth param 1) := lt_trans (code_left_lt_or a b) hlen
    have hlb : b < len (nth param 1) := lt_trans (code_right_lt_or a b) hlen
    have hn : neg PA194PAeq.language a ^⋏ neg PA194PAeq.language b < len (nth param 1) := by simpa [ha,hb] using hnlen
    have hna : neg PA194PAeq.language a < len (nth param 1) := lt_trans (code_left_lt_and _ _) hn
    have hnb : neg PA194PAeq.language b < len (nth param 1) := lt_trans (code_right_lt_and _ _) hn
    have hta := (formula_scope_translate ha s n param hs.1 hparam hla).isUFormula
    have htb := (formula_scope_translate hb s n param hs.2 hparam hlb).isUFormula
    rw [neg_or ha hb,translate_and param _ _ ha.neg hb.neg,
      translate_or param a b ha hb,iha s n param hs.1 hparam hla hna,ihb s n param hs.2 hparam hlb hnb,neg_or hta htb]
  · intro a ha ih s n param hscope hparam hlen hnlen
    have hs : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.all).mp hscope
    have hchild := formulaChildParameters_valid hparam
    have hla : a < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans (code_lt_all a) hlen
    have hn : neg PA194PAeq.language a < len (nth (formulaChildParameters param) 1) := by
      have hn' : (^∃ (neg PA194PAeq.language a)) < len (nth param 1) := by simpa [ha] using hnlen
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans (code_lt_exs _) hn'
    have hta := (formula_scope_translate ha (s+1) (n+1) (formulaChildParameters param) hs hchild hla).isUFormula
    have hdom : IsUFormula SourceL (domainCode (^#(0 : V))) := (domainCode_valid (show IsSemiterm SourceL (n+1) (^#(0 : V)) by simp)).isUFormula
    rw [neg_all ha,translate_exs param _ ha.neg,translate_all param a ha,ih (s+1) (n+1) (formulaChildParameters param) hs hchild hla hn]
    simp [allOutput,exsOutput,imp,hdom,hta]
  · intro a ha ih s n param hscope hparam hlen hnlen
    have hs : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.exs).mp hscope
    have hchild := formulaChildParameters_valid hparam
    have hla : a < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans (code_lt_exs a) hlen
    have hn : neg PA194PAeq.language a < len (nth (formulaChildParameters param) 1) := by
      have hn' : (^∀ (neg PA194PAeq.language a)) < len (nth param 1) := by simpa [ha] using hnlen
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans (code_lt_all _) hn'
    have hta := (formula_scope_translate ha (s+1) (n+1) (formulaChildParameters param) hs hchild hla).isUFormula
    have hdom : IsUFormula SourceL (domainCode (^#(0 : V))) := (domainCode_valid (show IsSemiterm SourceL (n+1) (^#(0 : V)) by simp)).isUFormula
    rw [neg_ex ha,translate_all param _ ha.neg,translate_exs param a ha,ih (s+1) (n+1) (formulaChildParameters param) hs hchild hla hn]
    simp [allOutput,exsOutput,imp,hdom,hta]
#print axioms NegationProperty_definable
#print axioms translateFormula_neg
end generic
end PA194FormulaDispatcher
