import PA194TermDispatcherEquations
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TermDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194PAeqTermFormulaTree
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
instance translate_defined : 𝚺₁-Function₂ (translate : V → V → V) via translateGraph := .mk fun v => by
  change translateGraph.val.Evalb v ↔ v 0 = translate (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using translate_graph (v 0) (v 1) (v 2)

def ScopeProperty (t : V) : Prop :=
  ∀ s n param, IsSemiterm PA194PAeq.language s t → ParametersValid s n param →
    t < len (nth param 1) → IsSemiformula SourceL n (translate param t)

theorem ScopeProperty_definable : 𝚷₁-Predicate (ScopeProperty : V → Prop) := by
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  unfold ScopeProperty ParametersValid
  definability
theorem scope_translate {t : V} (ht : IsUTerm PA194PAeq.language t) : ScopeProperty t := by
  apply IsUTerm.induction 𝚷 ScopeProperty_definable ?_ ?_ ?_ t ht
  · intro i s n param hterm hparam hlen
    have hi : i < s := by simpa using hterm
    rw [translate_bound]
    exact variableValue_valid hparam.2.2 (hparam.1.nth hi)
  · intro i s n param hterm hparam hlen
    have hcode : i < (^&i : V) := by
      change i < pair (1 : V) i + 1
      exact lt_of_le_of_lt (le_pair_right (1 : V) i) (lt_add_one _)
    have hi : i < len (nth param 1) := lt_trans hcode hlen
    rw [translate_free]
    exact variableValue_valid hparam.2.2 (hparam.2.1.nth hi)
  · intro k f v hf hv ih s n param hterm hparam hlen
    have hsv : IsSemitermVec PA194PAeq.language k s v := ((IsSemiterm.func).mp hterm).2
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm
      subst v
      rw [translate_zero]
      exact zeroValue_valid hparam.2.2
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by simpa using hsv.nth (show (0 : V) < 1 by simp)
      have hca : a < len (nth param 1) := lt_trans (by simpa using (nth_lt_qqFunc_of_lt (k := (1 : V)) (f := (1 : V)) (v := (?[a] : V)) (i := (0 : V)) (by simp))) hlen
      have hcp : ParametersValid s (n+1) (childParameters param) := childParameters_valid hparam
      have hlen' : a < len (nth (childParameters param) 1) := by
        simpa [childParameters, shiftTerms_length hparam.2.1] using hca
      have hchild := ih 0 (by simp) s (n+1) (childParameters param) (by simpa using ha) hcp (by simpa using hlen')
      rw [translate_succ param a ha.isUTerm]
      exact successorValue_valid hparam.2.2 (by simpa using hchild)
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
      have ha : IsSemiterm PA194PAeq.language s a := by simpa using hsv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language s b := by simpa using hsv.nth (show (1 : V) < 2 by simp)
      have hca : a < len (nth param 1) := lt_trans (by simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V)) (i := (0 : V)) (by simp))) hlen
      have hcb : b < len (nth param 1) := lt_trans (by simpa using (nth_lt_qqFunc_of_lt (k := (2 : V)) (f := f) (v := (?[a,b] : V)) (i := (1 : V)) (by simp))) hlen
      have hp1 : ParametersValid s ((n+1)+1) (binaryParameters param 1) := binaryParameters_valid hparam (by simp)
      have hp0 : ParametersValid s ((n+1)+1) (binaryParameters param 0) := binaryParameters_valid hparam (by simp)
      have hf1 := shiftTerms_valid hparam.2.1
      have hlen1 : a < len (nth (binaryParameters param 1) 1) := by
        simpa [binaryParameters,shiftTerms_length hparam.2.1,shiftTerms_length hf1] using hca
      have hlen0 : b < len (nth (binaryParameters param 0) 1) := by
        simpa [binaryParameters,shiftTerms_length hparam.2.1,shiftTerms_length hf1] using hcb
      have hleft := ih 0 (by simp) s ((n+1)+1) (binaryParameters param 1) (by simpa using ha) hp1 (by simpa using hlen1)
      have hright := ih 1 (by simp) s ((n+1)+1) (binaryParameters param 0) (by simpa using hb) hp0 (by simpa using hlen0)
      rcases htwo with rfl | rfl
      · rw [translate_add param a b ha.isUTerm hb.isUTerm]
        exact binaryValue_valid _ hparam.2.2 (by simpa using hleft) (by simpa using hright)
      · rw [translate_mul param a b ha.isUTerm hb.isUTerm]
        exact binaryValue_valid _ hparam.2.2 (by simpa using hleft) (by simpa using hright)

#print axioms scope_translate
#print axioms ScopeProperty_definable
end generic
end PA194TermDispatcher
