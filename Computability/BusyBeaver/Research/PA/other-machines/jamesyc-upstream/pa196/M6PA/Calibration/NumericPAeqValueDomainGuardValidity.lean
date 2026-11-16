module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueDomainGuard
@[expose] public section

/-! Guarded arity of the model-length conjunction, proved by an explicitly
represented full-PA induction invariant. No semantic domain witnesses follow. -/
namespace M6.PA.NumericPAeqValueDomainGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] guardGraph
noncomputable def guardValidInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ env n, (∀ i<k, ∃ t, !nthDef t env i ∧ !((isSemiterm language).sigma) n t) →
    ∃ out, !guardGraph out env k ∧ !((isSemiformula language).sigma) n out”

theorem guardValid_invariant (k : V) : guardValidInvariant.Evalb ![k] ↔
    ∀ env n : V, (∀ i<k, IsSemiterm language n (nth env i)) →
      IsSemiformula language n (guard env k) := by
  simp [guardValidInvariant,guard_graph,Matrix.comp_vecCons'']

attribute [local irreducible] guardValidInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem guard_isSemiformula (env count n : V)
    (h : ∀ i<count, IsSemiterm language n (nth env i)) :
    IsSemiformula language n (guard env count) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ env n : V,
      (∀ i<k, IsSemiterm language n (nth env i)) →
        IsSemiformula language n (guard env k) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ env n : V, (∀ i<k, IsSemiterm language n (nth env i)) →
        IsSemiformula language n (guard env k)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb guardValidInvariant,by trivial,?_⟩
      intro k; simpa using (guardValid_invariant (V:=V) k).symm
    · intro env n _; rw [guard_zero]; simp
    · intro k ih env n h
      rw [guard_succ]
      exact IsSemiformula.and.mpr ⟨ih env n (fun i hi => h i (lt_trans hi (lt_add_one k))),
        NumericPAeqTerm.domainCode_isSemiformula (h k (lt_add_one k))⟩
  exact hall count env n h

theorem guard_vector_isSemiformula {env count n : V}
    (h : IsSemitermVec language count n env) :
    IsSemiformula language n (guard env count) :=
  guard_isSemiformula env count n (fun _ hi => h.nth hi)

#print axioms guardValid_invariant
#print axioms guard_isSemiformula
#print axioms guard_vector_isSemiformula
end M6.PA.NumericPAeqValueDomainGuard

