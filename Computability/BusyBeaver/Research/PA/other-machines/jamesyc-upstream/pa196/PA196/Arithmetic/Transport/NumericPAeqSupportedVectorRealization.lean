module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Genuine full-PA original-source-rank induction for supported vector realization.
All actual value and domain assumptions remain inside the certified implication. -/
namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem vector_step (t:V) (ih:∀u<t,VectorSupply (V:=V) u) : VectorSupply (V:=V) t := by
  intro s r b f a w h native lo z hc
  rcases IsUTerm.case_iff.mp h.2.2.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,fn,ts,hfn,hvec,rfl⟩
  · exact vector_bvar_certificate h native lo z hc
  · exact vector_fvar_certificate h native lo z hc
  · rcases (Presentation.source_functions k fn).mp hfn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hvec
      subst ts; exact vector_zero_certificate h native lo z hc
    · obtain ⟨v,rfl⟩ := eq_singleton_iff_len_eq_one.mp hvec.lh.symm
      exact vector_successor_step (ih v (unary_child_rank v)) s r b f a w h native lo z hc
    · obtain ⟨v,v₂,hv,hw,rfl⟩ := IsUTermVec.two_iff.mp hvec
      exact vector_binary_step (ih v (binary_left_rank fn v v₂))
        (ih v₂ (binary_right_rank fn v v₂)) htag s r b f a w h native lo z hc

attribute [local irreducible] vectorInvariant
theorem open_source_value_vector (t:V) : VectorSupply (V:=V) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀t<k,VectorSupply (V:=V) t := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun k:V => ∀t<k,VectorSupply (V:=V) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb vectorInvariant,by trivial,?_⟩
      intro k; simpa using (vector_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact vector_step k ih
      · exact ih t hlt
  exact hall (t+1) t (lt_add_one t)

theorem open_source_vector_realization_certificate {s r b f a w t:V}
    (h:SupportedVectorEnvironment s r b f a w t) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (NumericPAeqValueVectorRealization.vectorCode s r b f a w t)):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (NumericPAeqValueVectorRealization.vectorCode s r b f a w t)+1 :=
  open_source_value_vector t s r b f a w h native lo z hc
#print axioms vector_step
#print axioms open_source_value_vector
#print axioms open_source_vector_realization_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
