module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueRealizationGuard
public import M6PA.Calibration.NumericPAeqTermValidity
@[expose] public section
namespace M6.PA.NumericPAeqValueRealizationGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] guardGraph entryGraph
noncomputable def guardValidInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ b f w a n, (∀ i<k, ∃ e, !entryGraph e b f w a i ∧ !((isSemiformula language).sigma) n e) →
    ∃ out, !guardGraph out b f w a k ∧ !((isSemiformula language).sigma) n out”
theorem guardValid_invariant (k:V):guardValidInvariant.Evalb ![k] ↔
    ∀b f w a n:V,(∀i<k,IsSemiformula language n (entry b f w a i))→
      IsSemiformula language n (guard b f w a k) := by
  simp [guardValidInvariant,entry_graph,guard_graph,Matrix.comp_vecCons'']
attribute [local irreducible] guardValidInvariant
theorem guard_isSemiformula (b f w a count n:V)
    (h:∀i<count,IsSemiformula language n (entry b f w a i)):
    IsSemiformula language n (guard b f w a count) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀b f w a n:V,(∀i<k,IsSemiformula language n (entry b f w a i))→
      IsSemiformula language n (guard b f w a k) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀b f w a n:V,
      (∀i<k,IsSemiformula language n (entry b f w a i))→IsSemiformula language n (guard b f w a k)) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb guardValidInvariant,by trivial,?_⟩
      intro k; simpa using (guardValid_invariant (V:=V) k).symm
    · intro b f w a n _; rw [guard_zero]; simp
    · intro k ih b f w a n h
      rw [guard_succ]
      exact IsSemiformula.and.mpr ⟨ih b f w a n (fun i hi=>h i (lt_trans hi (lt_add_one k))),h k (lt_add_one k)⟩
  exact hall count b f w a n h

theorem guard_vector_isSemiformula {b f w a s r n:V}
    (hb:IsSemitermVec language r n b) (hf:IsSemitermVec language (len f) n f)
    (hw:IsSemitermVec Presentation.language s r w) (ha:IsSemitermVec language s n a)
    (hbound:∀i<s,nth w i≤len f):IsSemiformula language n (guard b f w a s) := by
  apply guard_isSemiformula
  intro i hi
  apply valueSyntax_isSemiformula
  refine ⟨?_,hw.nth hi,?_⟩
  · simpa [ParametersValid] using And.intro hb (And.intro hf (ha.nth hi))
  · simpa using hbound i hi
#print axioms guardValid_invariant
#print axioms guard_isSemiformula
#print axioms guard_vector_isSemiformula
end M6.PA.NumericPAeqValueRealizationGuard

