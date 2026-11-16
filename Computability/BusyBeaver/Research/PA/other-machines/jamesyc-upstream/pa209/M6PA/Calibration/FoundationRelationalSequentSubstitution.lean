module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentSubstitutionLabels
@[expose] public section

/-! Exact all-model formula substitution compatibility for finite guarded
term-label environments, with the actual qVec binder change. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] parametersGraph translateGraph labelSubstitutionGraph
noncomputable def substitutionAgreementGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “p w a b f lo z. ∃ sp source target out, !(substsGraph language) sp w p ∧
    !parametersGraph source a f lo z ∧ !parametersGraph target b f lo z ∧
    !translateGraph out target sp ∧ !translateGraph out source p”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem substitutionAgreement_graph (p w a b f lo z : V) :
    substitutionAgreementGraph.val.Evalb ![p,w,a,b,f,lo,z] ↔
      translate (parameters b f lo z) (Bootstrapping.subst language w p)=
        translate (parameters a f lo z) p := by
  simp [substitutionAgreementGraph,parameters_graph,translate_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] substitutionAgreementGraph
noncomputable def substitutionAgreementInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, ∀ w a b f lo z, !labelSubstitutionGraph w a b f →
    ∀ k, !lenDef k a → !((isSemiformula language).sigma) k p →
      !substitutionAgreementGraph p w a b f lo z”

theorem substitutionAgreement_invariant (n : V) :
    substitutionAgreementInvariant.Evalb ![n] ↔
      ∀ p<n, ∀ w a b f lo z : V, LabelSubstitution w a b f →
        IsSemiformula language (len a) p →
        translate (parameters b f lo z) (Bootstrapping.subst language w p)=
          translate (parameters a f lo z) p := by
  simp [substitutionAgreementInvariant,labelSubstitution_graph,
    substitutionAgreement_graph,Matrix.comp_vecCons'']

attribute [local irreducible] translate substitutionAgreementInvariant

private theorem substitution_source_step (p : V)
    (ih : ∀ q<p, ∀ w a b f lo z : V, LabelSubstitution w a b f →
      IsSemiformula language (len a) q →
      translate (parameters b f lo z) (Bootstrapping.subst language w q)=
        translate (parameters a f lo z) q) :
    ∀ w a b f lo z : V, LabelSubstitution w a b f → IsSemiformula language (len a) p →
      translate (parameters b f lo z) (Bootstrapping.subst language w p)=
        translate (parameters a f lo z) p := by
  intro w a b f lo z hw hvalid
  rcases IsSemiformula.case_iff.mp hvalid with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [Bootstrapping.substs_rel hr ht.isUTerm,
      translate_rel _ _ _ _ hr (hw.isSemitermVec.termSubstVec ht).isUTerm,
      translate_rel _ _ _ _ hr ht.isUTerm]
    have hk := ((source_relations _ _).mp hr).1
    subst k
    exact totalAtom_termSubstVec r hw ht
  · rw [Bootstrapping.substs_nrel hr ht.isUTerm,
      translate_nrel _ _ _ _ hr (hw.isSemitermVec.termSubstVec ht).isUTerm,
      translate_nrel _ _ _ _ hr ht.isUTerm]
    have hk := ((source_relations _ _).mp hr).1
    subst k
    rw [totalAtom_termSubstVec r hw ht]
  · rw [Bootstrapping.substs_verum,translate_verum,translate_verum]
  · rw [Bootstrapping.substs_falsum,translate_falsum,translate_falsum]
  · rw [Bootstrapping.substs_and hp.isUFormula hq.isUFormula,
      translate_and _ _ _ (hp.subst hw.isSemitermVec).isUFormula (hq.subst hw.isSemitermVec).isUFormula,
      translate_and _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_K!_left p q) w a b f lo z hw hp,ih q (lt_K!_right p q) w a b f lo z hw hq]
  · rw [Bootstrapping.substs_or hp.isUFormula hq.isUFormula,
      translate_or _ _ _ (hp.subst hw.isSemitermVec).isUFormula (hq.subst hw.isSemitermVec).isUFormula,
      translate_or _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_or_left p q) w a b f lo z hw hp,ih q (lt_or_right p q) w a b f lo z hw hq]
  · have hp' : IsSemiformula language (len (lo∷a)) p := by simpa using hp
    have hh := ih p (lt_forall p) (qVec language w) (lo∷a) (lo∷b) f (lo+1) z (hw.qVec lo) hp'
    have hsub := hp.subst hw.isSemitermVec.qVec
    rw [Bootstrapping.substs_all hp.isUFormula,translate_all _ _ hsub.isUFormula,
      translate_all _ _ hp.isUFormula]
    simpa only [advance_parameters,parameters_allocator,hh]
  · have hp' : IsSemiformula language (len (lo∷a)) p := by simpa using hp
    have hh := ih p (lt_exists p) (qVec language w) (lo∷a) (lo∷b) f (lo+1) z (hw.qVec lo) hp'
    have hsub := hp.subst hw.isSemitermVec.qVec
    rw [Bootstrapping.substs_ex hp.isUFormula,translate_exs _ _ hsub.isUFormula,
      translate_exs _ _ hp.isUFormula]
    simpa only [advance_parameters,parameters_allocator,hh]

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_subst (p w a b f lo z : V) (hw : LabelSubstitution w a b f)
    (hp : IsSemiformula language (len a) p) :
    translate (parameters b f lo z) (Bootstrapping.subst language w p)=
      translate (parameters a f lo z) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, ∀ w a b f lo z : V, LabelSubstitution w a b f →
      IsSemiformula language (len a) p →
      translate (parameters b f lo z) (Bootstrapping.subst language w p)=
        translate (parameters a f lo z) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, ∀ w a b f lo z : V, LabelSubstitution w a b f →
        IsSemiformula language (len a) p →
        translate (parameters b f lo z) (Bootstrapping.subst language w p)=
          translate (parameters a f lo z) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb substitutionAgreementInvariant,by trivial,?_⟩
      intro n
      simpa using (substitutionAgreement_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact substitution_source_step n ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) w a b f lo z hw hp

noncomputable def substitutionAgreementSentence : ArithmeticSentence :=
  “∀ p w a b f lo z, !labelSubstitutionGraph w a b f →
    ∀ k, !lenDef k a → !((isSemiformula language).sigma) k p →
      !substitutionAgreementGraph p w a b f lo z”

theorem pa_proves_substitutionAgreement : theory ⊢ substitutionAgreementSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [substitutionAgreementSentence,models_iff,labelSubstitution_graph,
    substitutionAgreement_graph,Matrix.comp_vecCons'']
  intro p w a b f lo z hw hp
  exact translate_subst p w a b f lo z hw hp

#print axioms pa_proves_substitutionAgreement
#print axioms substitutionAgreement_graph
#print axioms substitutionAgreement_invariant
#print axioms substitution_source_step
#print axioms translate_subst
end M6.PA.RelationalSource.Numeric

