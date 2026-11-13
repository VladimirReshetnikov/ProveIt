module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentPaddedProofEnvironment
@[expose] public section

/-! Exact translation equality from a conservative finite prefix agreement.
The source and all environments may be nonstandard model codes. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def freePrefixGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “p f g. ∀ i<p, ∃ a, !nthDef a f i ∧ !nthDef a g i”

theorem freePrefix_graph (p f g : V) :
    freePrefixGraph.val.Evalb ![p,f,g] ↔ ∀ i<p, nth f i=nth g i := by
  simp [freePrefixGraph,eq_comm]

attribute [local irreducible] parametersGraph translateGraph freePrefixGraph
noncomputable def prefixAgreementGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “p b f g lo z. ∃ left right out,
    !parametersGraph left b f lo z ∧ !parametersGraph right b g lo z ∧
    !translateGraph out left p ∧ !translateGraph out right p”

theorem prefixAgreement_graph (p b f g lo z : V) :
    prefixAgreementGraph.val.Evalb ![p,b,f,g,lo,z] ↔
      translate (parameters b f lo z) p=translate (parameters b g lo z) p := by
  simp [prefixAgreementGraph,parameters_graph,translate_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] prefixAgreementGraph
noncomputable def prefixAgreementInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, !((isUFormula language).sigma) p →
    ∀ b f g lo z, !freePrefixGraph p f g → !prefixAgreementGraph p b f g lo z”

theorem prefixAgreement_invariant (n : V) :
    prefixAgreementInvariant.Evalb ![n] ↔ ∀ p<n, IsUFormula language p →
      ∀ b f g lo z : V, (∀ i<p, nth f i=nth g i) →
        translate (parameters b f lo z) p=translate (parameters b g lo z) p := by
  simp [prefixAgreementInvariant,freePrefix_graph,prefixAgreement_graph,Matrix.comp_vecCons'']

theorem totalLabel_prefix {p t b f g : V} (ht : IsUTerm language t)
    (hbound : t<p) (h : ∀ i<p, nth f i=nth g i) :
    totalLabel t b f=totalLabel t b g := by
  have hc : (∃ i, t=qqBvar i) ∨ ∃ i, t=qqFvar i := by
    simpa only [IsUTerm.case_iff,source_no_functions,false_and,exists_false,or_false] using ht
  rcases hc with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · simp
  · simp only [totalLabel_fvar]
    exact h i (lt_trans (var_lt_qqFvar i) hbound)

attribute [local irreducible] translate prefixAgreementInvariant
private theorem prefix_source_step (p : V) (hvalid : IsUFormula language p)
    (ih : ∀ q<p, IsUFormula language q → ∀ b f g lo z : V,
      (∀ i<q, nth f i=nth g i) →
      translate (parameters b f lo z) q=translate (parameters b g lo z) q) :
    ∀ b f g lo z : V, (∀ i<p, nth f i=nth g i) →
      translate (parameters b f lo z) p=translate (parameters b g lo z) p := by
  intro b f g lo z h
  rcases IsUFormula.case_iff.mp hvalid with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [translate_rel _ _ _ _ hr ht,translate_rel _ _ _ _ hr ht]
    have hk := ((source_relations _ _).mp hr).1
    subst k
    simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve]
    rw [totalLabel_prefix (ht.nth (by simp)) (nth_lt_qqRel_of_lt (by rw [← ht.lh]; simp)) h,
      totalLabel_prefix (ht.nth (by simp)) (nth_lt_qqRel_of_lt (by rw [← ht.lh]; simp)) h]
  · rw [translate_nrel _ _ _ _ hr ht,translate_nrel _ _ _ _ hr ht]
    have hk := ((source_relations _ _).mp hr).1
    subst k
    simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve]
    rw [totalLabel_prefix (ht.nth (by simp)) (nth_lt_qqNRel_of_lt (by rw [← ht.lh]; simp)) h,
      totalLabel_prefix (ht.nth (by simp)) (nth_lt_qqNRel_of_lt (by rw [← ht.lh]; simp)) h]
  · rw [translate_verum,translate_verum]
  · rw [translate_falsum,translate_falsum]
  · rw [translate_and _ _ _ hp hq,translate_and _ _ _ hp hq,
      ih p (lt_K!_left p q) hp b f g lo z (fun i hi => h i (lt_trans hi (lt_K!_left p q))),
      ih q (lt_K!_right p q) hq b f g lo z (fun i hi => h i (lt_trans hi (lt_K!_right p q)))]
  · rw [translate_or _ _ _ hp hq,translate_or _ _ _ hp hq,
      ih p (lt_or_left p q) hp b f g lo z (fun i hi => h i (lt_trans hi (lt_or_left p q))),
      ih q (lt_or_right p q) hq b f g lo z (fun i hi => h i (lt_trans hi (lt_or_right p q)))]
  · rw [translate_all _ _ hp,translate_all _ _ hp]
    simp only [advance_parameters,parameters_allocator]
    rw [ih p (lt_forall p) hp (lo∷b) f g (lo+1) z (fun i hi => h i (lt_trans hi (lt_forall p)))]
  · rw [translate_exs _ _ hp,translate_exs _ _ hp]
    simp only [advance_parameters,parameters_allocator]
    rw [ih p (lt_exists p) hp (lo∷b) f g (lo+1) z (fun i hi => h i (lt_trans hi (lt_exists p)))]

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem translate_free_prefix (p b f g lo z : V) (hp : IsUFormula language p)
    (h : ∀ i<p, nth f i=nth g i) :
    translate (parameters b f lo z) p=translate (parameters b g lo z) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, IsUFormula language p → ∀ b f g lo z : V,
      (∀ i<p, nth f i=nth g i) →
      translate (parameters b f lo z) p=translate (parameters b g lo z) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, IsUFormula language p → ∀ b f g lo z : V,
        (∀ i<p, nth f i=nth g i) →
        translate (parameters b f lo z) p=translate (parameters b g lo z) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb prefixAgreementInvariant,by trivial,?_⟩
      intro n
      simpa using (prefixAgreement_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact fun hp => prefix_source_step n hp ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) hp b f g lo z h

theorem translate_padEnvironment (p b f lo z n : V) (hp : IsUFormula language p)
    (hf : p≤len f) :
    translate (parameters b (padEnvironment f n) lo z) p=translate (parameters b f lo z) p :=
  translate_free_prefix _ _ _ _ _ _ hp (fun i hi =>
    (padEnvironment_properties f n).2.1 i (lt_of_lt_of_le hi hf))

#print axioms freePrefix_graph
#print axioms prefixAgreement_graph
#print axioms prefixAgreement_invariant
#print axioms translate_free_prefix
#print axioms translate_padEnvironment
end M6.PA.RelationalSource.Numeric

