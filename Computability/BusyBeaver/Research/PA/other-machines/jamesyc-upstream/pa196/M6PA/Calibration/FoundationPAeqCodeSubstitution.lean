module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionGraph
@[expose] public section

/-! Literal source/target formula substitution compatibility, including lifted
vectors beneath quantifiers. The displayed arbitrary-parameter course-of-values
invariant is justified by full PA, not standard-Nat induction. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem substitution_step (p : V)
    (ih : ∀ q<p, ∀ k n w param : V, IsSemiformula ℒₒᵣ k q → IsSemitermVec ℒₒᵣ k n w →
      formulaCode param (subst ℒₒᵣ w q)=subst Presentation.language (termVector k w) (formulaCode param q)) :
    ∀ k n w param : V, IsSemiformula ℒₒᵣ k p → IsSemitermVec ℒₒᵣ k n w →
      formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p) := by
  intro k n w param hvalid hw
  rcases IsSemiformula.case_iff.mp hvalid with
    ⟨a,r,ts,hr,ht,rfl⟩ | ⟨a,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [substs_rel hr ht.isUTerm,formulaCode_rel _ _ _ _ hr (hw.termSubstVec ht).isUTerm,
      formulaCode_rel _ _ _ _ hr ht.isUTerm]
    exact atomCode_subst param hr hw ht
  · rw [substs_nrel hr ht.isUTerm,formulaCode_nrel _ _ _ _ hr (hw.termSubstVec ht).isUTerm,
      formulaCode_nrel _ _ _ _ hr ht.isUTerm,atomCode_subst param hr hw ht,
      substs_neg (atom_valid param hr ht) (termVector_valid hw)]
  · rw [substs_verum,formulaCode_verum,substs_verum]
  · rw [substs_falsum,formulaCode_falsum,substs_falsum]
  · rw [substs_and hp.isUFormula hq.isUFormula,
      formulaCode_and _ _ _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      formulaCode_and _ _ _ hp.isUFormula hq.isUFormula,
      substs_and (formulaCode_valid param hp).isUFormula (formulaCode_valid param hq).isUFormula,
      ih p (lt_K!_left p q) k n w param hp hw,ih q (lt_K!_right p q) k n w param hq hw]
  · rw [substs_or hp.isUFormula hq.isUFormula,
      formulaCode_or _ _ _ (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      formulaCode_or _ _ _ hp.isUFormula hq.isUFormula,
      substs_or (formulaCode_valid param hp).isUFormula (formulaCode_valid param hq).isUFormula,
      ih p (lt_or_left p q) k n w param hp hw,ih q (lt_or_right p q) k n w param hq hw]
  · rw [substs_all hp.isUFormula,formulaCode_all _ _ (hp.subst hw.qVec).isUFormula,
      formulaCode_all _ _ hp.isUFormula,substs_all (formulaCode_valid param hp).isUFormula,
      ih p (lt_forall p) (k+1) (n+1) (qVec ℒₒᵣ w) param hp hw.qVec,termVector_qVec hw.isUTerm]
  · rw [substs_ex hp.isUFormula,formulaCode_exs _ _ (hp.subst hw.qVec).isUFormula,
      formulaCode_exs _ _ hp.isUFormula,substs_ex (formulaCode_valid param hp).isUFormula,
      ih p (lt_exists p) (k+1) (n+1) (qVec ℒₒᵣ w) param hp hw.qVec,termVector_qVec hw.isUTerm]

attribute [local irreducible] substitutionInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaCode_subst (param : V) {k n w p : V}
    (hp : IsSemiformula ℒₒᵣ k p) (hw : IsSemitermVec ℒₒᵣ k n w) :
    formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ b : V, ∀ p<b, ∀ k n w param : V,
      IsSemiformula ℒₒᵣ k p → IsSemitermVec ℒₒᵣ k n w →
      formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun b : V => ∀ p<b, ∀ k n w param : V,
      IsSemiformula ℒₒᵣ k p → IsSemitermVec ℒₒᵣ k n w →
      formulaCode param (subst ℒₒᵣ w p)=subst Presentation.language (termVector k w) (formulaCode param p)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb substitutionInvariant,by trivial,?_⟩
      intro b; simpa using (substitution_invariant (V:=V) b).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro b ih p hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact substitution_step b ih
      · exact ih p hlt
  exact hall (p+1) p (lt_add_one p) k n w param hp hw

noncomputable def substitutionSentence : ArithmeticSentence :=
  “∀ param p k n w, !((isSemiformula ℒₒᵣ).sigma) k p → !((isSemitermVec ℒₒᵣ).sigma) k n w →
    !substitutionAgreementGraph param p k w”
theorem pa_proves_substitution : theory ⊢ substitutionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [substitutionSentence,models_iff,substitutionAgreement_graph,Matrix.comp_vecCons'']
  intro param p k n w hp hw
  exact formulaCode_subst param hp hw

#print axioms substitution_step
#print axioms formulaCode_subst
#print axioms pa_proves_substitution
end M6.PA.FoundationPAeqCode

