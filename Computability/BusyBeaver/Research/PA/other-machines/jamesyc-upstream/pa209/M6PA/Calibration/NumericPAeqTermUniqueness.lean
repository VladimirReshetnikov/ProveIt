module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTotality
public import M6PA.Calibration.NumericPAeqTermInversion
@[expose] public section

/-! Output uniqueness of finite witness tables follows genuine full-PA
induction on the source term code. Tables themselves need not be unique. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] valueWitnessGraph
noncomputable def uniquenessInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ t<n, !((isUTerm Presentation.language).sigma) t →
    ∀ param a b, !valueWitnessGraph a param t → !valueWitnessGraph b param t → a=b”
theorem uniqueness_invariant (n : V) : uniquenessInvariant.Evalb ![n] ↔
    ∀ t<n, IsUTerm Presentation.language t → ∀ param a b,
      ValueWitness param t a → ValueWitness param t b → a=b := by
  simp [uniquenessInvariant,valueWitness_graph,Matrix.comp_vecCons'']

private theorem uniqueness_step (t : V) (ht : IsUTerm Presentation.language t)
    (ih : ∀ u<t, IsUTerm Presentation.language u → ∀ param a b,
      ValueWitness param u a → ValueWitness param u b → a=b) :
    ∀ param a b, ValueWitness param t a → ValueWitness param t b → a=b := by
  intro param a b ha hb
  rcases IsUTerm.case_iff.mp ht with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · exact ((witness_bvar_iff _ _ _).mp ha).trans ((witness_bvar_iff _ _ _).mp hb).symm
  · exact ((witness_fvar_iff _ _ _).mp ha).trans ((witness_fvar_iff _ _ _).mp hb).symm
  · rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts
      exact ((witness_zero_iff _ _).mp ha).trans ((witness_zero_iff _ _).mp hb).symm
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      obtain ⟨x,hx,rfl⟩ := (witness_successor_iff _ _ _).mp ha
      obtain ⟨y,hy,rfl⟩ := (witness_successor_iff _ _ _).mp hb
      rw [ih u (unary_child_rank u) (IsUTermVec.adjoin₁_iff.mp hv) _ x y hx hy]
    · obtain ⟨u,v,hu,hv',rfl⟩ := IsUTermVec.two_iff.mp hv
      rcases htag with rfl|rfl
      · obtain ⟨x1,x2,hx1,hx2,rfl⟩ := (witness_addition_iff _ _ _ _).mp ha
        obtain ⟨y1,y2,hy1,hy2,rfl⟩ := (witness_addition_iff _ _ _ _).mp hb
        rw [ih u (binary_left_rank 2 u v) hu _ x1 y1 hx1 hy1,
          ih v (binary_right_rank 2 u v) hv' _ x2 y2 hx2 hy2]
      · obtain ⟨x1,x2,hx1,hx2,rfl⟩ := (witness_multiplication_iff _ _ _ _).mp ha
        obtain ⟨y1,y2,hy1,hy2,rfl⟩ := (witness_multiplication_iff _ _ _ _).mp hb
        rw [ih u (binary_left_rank 3 u v) hu _ x1 y1 hx1 hy1,
          ih v (binary_right_rank 3 u v) hv' _ x2 y2 hx2 hy2]

attribute [local irreducible] uniquenessInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem valueWitness_unique (t param a b : V) (ht : IsUTerm Presentation.language t)
    (ha : ValueWitness param t a) (hb : ValueWitness param t b) : a=b := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ t<n, IsUTerm Presentation.language t → ∀ param a b,
      ValueWitness param t a → ValueWitness param t b → a=b := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ t<n, IsUTerm Presentation.language t → ∀ param a b,
        ValueWitness param t a → ValueWitness param t b → a=b) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb uniquenessInvariant,by trivial,?_⟩
      intro n; simpa using (uniqueness_invariant (V:=V) n).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro n ih t ht hvalid param a b ha hb
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact uniqueness_step n hvalid ih param a b ha hb
      · exact ih t hlt hvalid param a b ha hb
  exact hall (t+1) t (lt_add_one t) ht param a b ha hb

theorem valueWitness_exists_unique (t param : V) (ht : IsUTerm Presentation.language t) :
    ∃! out, ValueWitness param t out := by
  obtain ⟨out,ho⟩ := valueWitness_exists t param ht
  exact ⟨out,ho,fun y hy => valueWitness_unique t param y out ht hy ho⟩

#print axioms uniqueness_invariant
#print axioms uniqueness_step
#print axioms valueWitness_unique
#print axioms valueWitness_exists_unique
end M6.PA.NumericPAeqTerm

