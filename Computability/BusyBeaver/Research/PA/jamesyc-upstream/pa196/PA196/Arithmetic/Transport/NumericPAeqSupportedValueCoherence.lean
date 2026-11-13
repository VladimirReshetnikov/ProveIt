module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceInvariant
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceSuccessorSupply
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceBinarySupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueCoherence


/-! Genuine full-PA source-rank induction supplies guarded semantic value
coherence for arbitrary model-valued arithmetic terms, at requested labels. -/
namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueCoherence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem coherence_step (t:V) (ih:∀u<t,SupportedCoherenceSupply (V:=V) u) : SupportedCoherenceSupply (V:=V) t := by
  intro s b c f g h native lo z hc
  rcases IsUTerm.case_iff.mp h.1.2.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,fn,ts,hfn,hvec,rfl⟩
  · exact coherence_bvar_certificate h native lo z hc
  · exact coherence_fvar_certificate h native lo z hc
  · rcases (Presentation.source_functions k fn).mp hfn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hvec
      subst ts; exact coherence_zero_certificate h native lo z hc
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hvec.lh.symm
      exact coherence_successor_step (ih u (unary_child_rank u)) s b c f g h native lo z hc
    · obtain ⟨u,v,hu,hv,rfl⟩ := IsUTermVec.two_iff.mp hvec
      have ihu := ih u (binary_left_rank fn u v)
      have ihv := ih v (binary_right_rank fn u v)
      rcases htag with rfl|rfl
      · exact coherence_addition_step ihu ihv s b c f g h native lo z hc
      · exact coherence_multiplication_step ihu ihv s b c f g h native lo z hc

attribute [local irreducible] coherenceInvariant
theorem guarded_value_coherence (t:V) : SupportedCoherenceSupply (V:=V) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀t<k,SupportedCoherenceSupply (V:=V) t := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun k:V => ∀t<k,SupportedCoherenceSupply (V:=V) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb coherenceInvariant,by trivial,?_⟩
      intro k; simpa using (coherence_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact coherence_step k ih
      · exact ih t hlt
  exact hall (t+1) t (lt_add_one t)

theorem guarded_value_coherence_certificate {s b c f g t:V} (h:SupportedCoherenceEnvironment s b c f g t)
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g t)) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (coherenceCode s b c f g t)+1 := guarded_value_coherence t s b c f g h native lo z hc

#print axioms coherence_step
#print axioms guarded_value_coherence
#print axioms guarded_value_coherence_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
