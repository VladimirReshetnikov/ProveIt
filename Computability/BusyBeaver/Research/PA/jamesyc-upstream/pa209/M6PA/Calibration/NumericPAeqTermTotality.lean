module
public import M6PA.Calibration.NumericPAeqTermTables
public import M6PA.Theory
@[expose] public section

/-! Genuine full-PA, all-model source-code induction constructs a finite HFS
witness table for every well-formed source term and every parameter packet.
No environment validity or ordinal-object existence is needed for syntax. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] valueWitnessGraph
noncomputable def existenceInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ t<n, !((isUTerm Presentation.language).sigma) t → ∀ param, ∃ out, !valueWitnessGraph out param t”
theorem existence_invariant (n : V) : existenceInvariant.Evalb ![n] ↔
    ∀ t<n, IsUTerm Presentation.language t → ∀ param, ∃ out, ValueWitness param t out := by
  simp [existenceInvariant,valueWitness_graph,Matrix.comp_vecCons'']

private theorem existence_step (t : V) (ht : IsUTerm Presentation.language t)
    (ih : ∀ u<t, IsUTerm Presentation.language u → ∀ param, ∃ out, ValueWitness param u out) :
    ∀ param, ∃ out, ValueWitness param t out := by
  intro param
  rcases IsUTerm.case_iff.mp ht with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · exact ⟨_,witness_bvar param i⟩
  · exact ⟨_,witness_fvar param i⟩
  · rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; exact ⟨_,witness_zero param⟩
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      obtain ⟨a,ha⟩ := ih u (unary_child_rank u) (IsUTermVec.adjoin₁_iff.mp hv) (childParameters param)
      exact ⟨_,witness_successor ha⟩
    · obtain ⟨u,v,hu,hv',rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨a,ha⟩ := ih u (binary_left_rank f u v) hu (binaryParameters param 1)
      obtain ⟨b,hb⟩ := ih v (binary_right_rank f u v) hv' (binaryParameters param 0)
      rcases htag with rfl|rfl
      · exact ⟨_,witness_addition ha hb⟩
      · exact ⟨_,witness_multiplication ha hb⟩

attribute [local irreducible] existenceInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem valueWitness_exists (t param : V) (ht : IsUTerm Presentation.language t) :
    ∃ out, ValueWitness param t out := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ t<n, IsUTerm Presentation.language t → ∀ param, ∃ out, ValueWitness param t out := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ t<n, IsUTerm Presentation.language t → ∀ param, ∃ out, ValueWitness param t out) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb existenceInvariant,by trivial,?_⟩
      intro n; simpa using (existence_invariant (V:=V) n).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro n ih t ht hvalid param
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact existence_step n hvalid ih param
      · exact ih t hlt hvalid param
  exact hall (t+1) t (lt_add_one t) ht param

noncomputable def existenceSentence : ArithmeticSentence :=
  “∀ t param, !((isUTerm Presentation.language).sigma) t → ∃ out, !valueWitnessGraph out param t”
theorem pa_proves_valueWitness_exists : theory ⊢ existenceSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [existenceSentence,models_iff,valueWitness_graph,Matrix.comp_vecCons'']
  intro t param ht
  exact valueWitness_exists t param ht

#print axioms existence_invariant
#print axioms existence_step
#print axioms valueWitness_exists
#print axioms pa_proves_valueWitness_exists
end M6.PA.NumericPAeqTerm

