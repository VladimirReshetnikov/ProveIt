module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueRealizationGuardValidity
public import M6PA.Calibration.NumericPAeqTermSupportedTargetShift
@[expose] public section
namespace M6.PA.NumericPAeqValueRealizationGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem entry_supported_targetShift {b f w a s r n i:V}
    (hb:IsSemitermVec language r n b) (hf:IsSemitermVec language (len f) n f)
    (hw:IsSemitermVec Presentation.language s r w) (ha:IsSemitermVec language s n a)
    (hs:FreeSupported (len f) (nth w i)) (hi:i<s) :
    shift language (entry b f w a i)=entry (targetShiftTerms b) (targetShiftTerms f) w (targetShiftTerms a) i := by
  have hc : SupportedTermCovered r n (parameters b f (nth a i)) (nth w i) :=
    ⟨by simpa [ParametersValid] using And.intro hb (And.intro hf (ha.nth hi)),hw.nth hi,by simpa using hs⟩
  unfold entry
  rw [valueSyntax_supported_targetShift hc]
  simp only [targetShiftParameters,parameters_bound,parameters_free,parameters_result,targetShiftTerms_nth ha hi]

attribute [local irreducible] guardGraph entryGraph
noncomputable def targetShiftInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ b f w a bs fs aa n,
    (∀ i<k, ∃ e es se, !entryGraph e b f w a i ∧ !entryGraph es bs fs w aa i ∧
      !((isSemiformula language).sigma) n e ∧ !(shiftGraph language) se e ∧ se=es) →
    ∃ g gs sg, !guardGraph g b f w a k ∧ !guardGraph gs bs fs w aa k ∧
      !(shiftGraph language) sg g ∧ sg=gs”
theorem targetShift_invariant (k:V) : targetShiftInvariant.Evalb ![k] ↔
    ∀b f w a bs fs aa n:V,
    (∀i<k,IsSemiformula language n (entry b f w a i) ∧
      shift language (entry b f w a i)=entry bs fs w aa i)→
    shift language (guard b f w a k)=guard bs fs w aa k := by
  simp [targetShiftInvariant,entry_graph,guard_graph,Matrix.comp_vecCons'']
attribute [local irreducible] targetShiftInvariant
theorem guard_targetShift_of_entries {b f w a bs fs aa n k:V}
    (h:∀i<k,IsSemiformula language n (entry b f w a i) ∧
      shift language (entry b f w a i)=entry bs fs w aa i) :
    shift language (guard b f w a k)=guard bs fs w aa k := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀b f w a bs fs aa n:V,
      (∀i<k,IsSemiformula language n (entry b f w a i) ∧ shift language (entry b f w a i)=entry bs fs w aa i)→
      shift language (guard b f w a k)=guard bs fs w aa k := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀b f w a bs fs aa n:V,
      (∀i<k,IsSemiformula language n (entry b f w a i) ∧ shift language (entry b f w a i)=entry bs fs w aa i)→
      shift language (guard b f w a k)=guard bs fs w aa k) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb targetShiftInvariant,by trivial,?_⟩
      intro k; simpa using (targetShift_invariant (V:=V) k).symm
    · intro b f w a bs fs aa n h; simp
    · intro k ih b f w a bs fs aa n h
      have hk := h k (lt_add_one k)
      have hprev := guard_isSemiformula b f w a k n (fun i hi=>(h i (lt_trans hi (lt_add_one k))).1)
      rw [guard_succ,guard_succ,shift_and hprev.isUFormula hk.1.isUFormula,
        ih b f w a bs fs aa n (fun i hi=>h i (lt_trans hi (lt_add_one k))),hk.2]
  exact hall k b f w a bs fs aa n h

theorem guard_supported_targetShift {b f w a s r n k:V}
    (hb:IsSemitermVec language r n b) (hf:IsSemitermVec language (len f) n f)
    (hw:IsSemitermVec Presentation.language s r w) (ha:IsSemitermVec language s n a)
    (hs:∀i<s,FreeSupported (len f) (nth w i)) (hk:k≤s) :
    shift language (guard b f w a k)=guard (targetShiftTerms b) (targetShiftTerms f) w (targetShiftTerms a) k := by
  apply guard_targetShift_of_entries (n:=n)
  intro i hi
  have his := lt_of_lt_of_le hi hk
  refine ⟨?_,entry_supported_targetShift hb hf hw ha (hs i his) his⟩
  apply valueSyntax_supported_isSemiformula
  exact ⟨by simpa [ParametersValid] using And.intro hb (And.intro hf (ha.nth his)),hw.nth his,by simpa using hs i his⟩
#print axioms entry_supported_targetShift
#print axioms targetShift_invariant
#print axioms guard_targetShift_of_entries
#print axioms guard_supported_targetShift
end M6.PA.NumericPAeqValueRealizationGuard
