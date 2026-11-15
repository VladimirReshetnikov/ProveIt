import PA194FormulaDispatcherEquations
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
instance translateFormula_defined : 𝚺₁-Function₂ (translateFormula : V → V → V) via translateFormulaGraph := .mk fun v => by
  change translateFormulaGraph.val.Evalb v ↔ v 0 = translateFormula (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using translateFormula_graph (v 0) (v 1) (v 2)
def FormulaScopeProperty (p : V) : Prop :=
  ∀ s n param, IsSemiformula PA194PAeq.language s p → ParametersValid s n param →
    p < len (nth param 1) → IsSemiformula SourceL n (translateFormula param p)
theorem FormulaScopeProperty_definable : 𝚷₁-Predicate (FormulaScopeProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translateFormula : V → V → V) := translateFormula_defined.to_definable
  unfold FormulaScopeProperty ParametersValid
  definability

theorem formula_scope_translate {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaScopeProperty p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaScopeProperty_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv s n param hscope hparam hlen
    have hsv := ((IsSemiformula.rel).mp hscope).2
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth param 1) := lt_trans (nth_lt_qqRel_of_lt (by simpa [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth param 1) := lt_trans (nth_lt_qqRel_of_lt (by simpa [←hv.lh])) hlen
    rw [translate_rel param _ _ _ hr hv]
    exact atomicEquality_valid hparam ha hb hla hlb
  · intro k r v hr hv s n param hscope hparam hlen
    have hsv := ((IsSemiformula.nrel).mp hscope).2
    rcases (PA194PAeq.source_relations k r).mp hr with ⟨rfl,rfl⟩
    have ha : IsSemiterm PA194PAeq.language s (nth v 0) := hsv.nth (by simp)
    have hb : IsSemiterm PA194PAeq.language s (nth v 1) := hsv.nth (by simp)
    have hla : nth v 0 < len (nth param 1) := lt_trans (nth_lt_qqNRel_of_lt (by simpa [←hv.lh])) hlen
    have hlb : nth v 1 < len (nth param 1) := lt_trans (nth_lt_qqNRel_of_lt (by simpa [←hv.lh])) hlen
    rw [translate_nrel param _ _ _ hr hv,IsSemiformula.neg_iff]
    exact atomicEquality_valid hparam ha hb hla hlb
  · intro s n param hscope hparam hlen
    simp [translate_verum]
  · intro s n param hscope hparam hlen
    simp [translate_falsum]
  · intro a b ha hb iha ihb s n param hscope hparam hlen
    have hsc := (IsSemiformula.and).mp hscope
    have ha' : a < (a ^⋏ b) := by
      change a < pair (4 : V) (pair a b) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_left a b) (le_pair_right (4 : V) (pair a b))) (lt_add_one _)
    have hb' : b < (a ^⋏ b) := by
      change b < pair (4 : V) (pair a b) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_right a b) (le_pair_right (4 : V) (pair a b))) (lt_add_one _)
    rw [translate_and param a b ha hb,IsSemiformula.and]
    exact ⟨iha s n param hsc.1 hparam (lt_trans ha' hlen),ihb s n param hsc.2 hparam (lt_trans hb' hlen)⟩
  · intro a b ha hb iha ihb s n param hscope hparam hlen
    have hsc := (IsSemiformula.or).mp hscope
    have ha' : a < (a ^⋎ b) := by
      change a < pair (5 : V) (pair a b) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_left a b) (le_pair_right (5 : V) (pair a b))) (lt_add_one _)
    have hb' : b < (a ^⋎ b) := by
      change b < pair (5 : V) (pair a b) + 1
      exact lt_of_le_of_lt (le_trans (le_pair_right a b) (le_pair_right (5 : V) (pair a b))) (lt_add_one _)
    rw [translate_or param a b ha hb,IsSemiformula.or]
    exact ⟨iha s n param hsc.1 hparam (lt_trans ha' hlen),ihb s n param hsc.2 hparam (lt_trans hb' hlen)⟩
  · intro a ha ih s n param hscope hparam hlen
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.all).mp hscope
    have ha' : a < (^∀ a) := by
      change a < pair (6 : V) a + 1
      exact lt_of_le_of_lt (le_pair_right (6 : V) a) (lt_add_one _)
    have hchild : ParametersValid (s+1) (n+1) (formulaChildParameters param) := formulaChildParameters_valid hparam
    have hlen' : a < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans ha' hlen
    have hc := ih (s+1) (n+1) (formulaChildParameters param) hsc hchild hlen'
    rw [translate_all param a ha]
    apply IsSemiformula.all.mpr
    apply IsSemiformula.imp.mpr
    exact ⟨domainCode_valid (by simp),hc⟩
  · intro a ha ih s n param hscope hparam hlen
    have hsc : IsSemiformula PA194PAeq.language (s+1) a := (IsSemiformula.exs).mp hscope
    have ha' : a < (^∃ a) := by
      change a < pair (7 : V) a + 1
      exact lt_of_le_of_lt (le_pair_right (7 : V) a) (lt_add_one _)
    have hchild : ParametersValid (s+1) (n+1) (formulaChildParameters param) := formulaChildParameters_valid hparam
    have hlen' : a < len (nth (formulaChildParameters param) 1) := by
      simpa [formulaChildParameters,shiftTerms_length hparam.2.1] using lt_trans ha' hlen
    have hc := ih (s+1) (n+1) (formulaChildParameters param) hsc hchild hlen'
    rw [translate_exs param a ha]
    apply IsSemiformula.exs.mpr
    exact IsSemiformula.and.mpr ⟨domainCode_valid (by simp),hc⟩
#print axioms translateFormula_defined
#print axioms FormulaScopeProperty_definable
#print axioms formula_scope_translate
end generic
end PA194FormulaDispatcher
