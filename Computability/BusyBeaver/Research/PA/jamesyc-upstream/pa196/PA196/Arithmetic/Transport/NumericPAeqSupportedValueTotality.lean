module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotalityInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueTotality


/-! Genuine full-PA source-rank induction supplies guarded semantic value
existence for arbitrary model-valued arithmetic terms, at requested labels. -/
namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm PA196.Arithmetic.Checker NumericPAeqValueTotality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem totality_step (t:V) (ih:∀u<t,ValueSupply (V:=V) u) : ValueSupply (V:=V) t := by
  intro s b f h g lo z hc
  rcases IsUTerm.case_iff.mp h.2.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,fn,ts,hfn,hvec,rfl⟩
  · exact guarded_bvar_certificate h g lo z hc
  · exact guarded_fvar_certificate h g lo z hc
  · rcases (Presentation.source_functions k fn).mp hfn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hvec
      subst ts; exact guarded_zero_certificate h g lo z hc
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hvec.lh.symm
      exact guarded_successor_step (ih u (unary_child_rank u)) s b f h g lo z hc
    · obtain ⟨u,v,hu,hv,rfl⟩ := IsUTermVec.two_iff.mp hvec
      have ihu := ih u (binary_left_rank fn u v)
      have ihv := ih v (binary_right_rank fn u v)
      rcases htag with rfl|rfl
      · exact guarded_addition_step ihu ihv s b f h g lo z hc
      · exact guarded_multiplication_step ihu ihv s b f h g lo z hc

attribute [local irreducible] totalityInvariant
theorem guarded_value_totality (t:V) : ValueSupply (V:=V) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀t<k,ValueSupply (V:=V) t := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun k:V => ∀t<k,ValueSupply (V:=V) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb totalityInvariant,by trivial,?_⟩
      intro k; simpa using (totality_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact totality_step k ih
      · exact ih t hlt
  exact hall (t+1) t (lt_add_one t)

theorem guarded_value_totality_certificate {s b f t:V} (h:SupportedValueEnvironment s b f t)
    (g lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (guardedTotalityCode s b f t)) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (guardedTotalityCode s b f t)+1 := guarded_value_totality t s b f h g lo z hc

#print axioms totality_step
#print axioms guarded_value_totality
#print axioms guarded_value_totality_certificate
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueTotality

