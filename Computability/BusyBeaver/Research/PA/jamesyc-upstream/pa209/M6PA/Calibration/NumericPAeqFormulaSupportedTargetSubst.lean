module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetSubstAtoms
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedTargetSubstGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “w param p. ∃ sp q sq tq, !targetSubstParametersGraph sp w param ∧
    !formulaSyntaxGraph q param p ∧ !formulaSyntaxGraph sq sp p ∧
    !(substsGraph language) tq w q ∧ tq=sq”
theorem supportedTargetSubst_graph (w param p : V) : supportedTargetSubstGraph.val.Evalb ![w,param,p] ↔
    subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p := by
  simp [supportedTargetSubstGraph,formulaSyntax_graph,targetSubstParameters_graph,Matrix.comp_vecCons'']
noncomputable def supportedTargetSubstInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n m w param, !supportedCoverageGraph s n param p → !((isSemitermVec language).sigma) n m w → !supportedTargetSubstGraph w param p”
theorem supportedTargetSubst_invariant (bound : V) : supportedTargetSubstInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n m w param, SupportedFormulaCovered s n param p → IsSemitermVec language n m w →
      subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p := by
  simp [supportedTargetSubstInvariant,supportedCoverage_graph,supportedTargetSubst_graph,Matrix.comp_vecCons'']
private theorem supportedTargetSubst_step (p : V)
    (ih : ∀ q<p, ∀ s n m w param, SupportedFormulaCovered s n param q → IsSemitermVec language n m w →
      subst language w (formulaSyntax param q)=formulaSyntax (targetSubstParameters w param) q) :
    ∀ s n m w param, SupportedFormulaCovered s n param p → IsSemitermVec language n m w →
      subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p := by
  intro s n m w param h hw
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · have ha := supported_coverage_rel h
    rw [formulaSyntax_rel _ _ _ _ hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr ht.isUTerm,
      atomCode_supported_targetSubst h.1 ha.2.2.1 hw ha.2.2.2]
  · have ha := supported_coverage_nrel h
    rw [formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,
      substs_neg (atomCode_supported_isSemiformula (k:=k) (r:=r) h.1 ha.2.2.1 ha.2.2.2) hw,
      atomCode_supported_targetSubst h.1 ha.2.2.1 hw ha.2.2.2]
  · simp only [formulaSyntax_verum,substs_verum]
  · simp only [formulaSyntax_falsum,substs_falsum]
  · have hc := supported_coverage_and h
    rw [formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      substs_and (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_K!_left p q) s n m w param hc.1 hw,ih q (lt_K!_right p q) s n m w param hc.2 hw]
  · have hc := supported_coverage_or h
    rw [formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      substs_or (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_or_left p q) s n m w param hc.1 hw,ih q (lt_or_right p q) s n m w param hc.2 hw]
  · have hc := supported_coverage_all h
    rw [formulaSyntax_all _ _ hp.isUFormula,formulaSyntax_all _ _ hp.isUFormula,
      guardedAllCode_targetSubst hw (formulaSyntax_supported_isSemiformula hc),
      ih p (lt_forall p) (s+1) (n+1) (m+1) (qVec language w) _ hc hw.qVec,targetSubstParameters_binder h.1 hw]
  · have hc := supported_coverage_exs h
    rw [formulaSyntax_exs _ _ hp.isUFormula,formulaSyntax_exs _ _ hp.isUFormula,
      guardedExsCode_targetSubst hw (formulaSyntax_supported_isSemiformula hc),
      ih p (lt_exists p) (s+1) (n+1) (m+1) (qVec language w) _ hc hw.qVec,targetSubstParameters_binder h.1 hw]
attribute [local irreducible] supportedTargetSubstInvariant
theorem formulaSyntax_supported_targetSubst {s n m w param p : V} (h : SupportedFormulaCovered s n param p) (hw : IsSemitermVec language n m w) :
    subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n m w param, SupportedFormulaCovered s n param p → IsSemitermVec language n m w →
      subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n m w param, SupportedFormulaCovered s n param p → IsSemitermVec language n m w →
        subst language w (formulaSyntax param p)=formulaSyntax (targetSubstParameters w param) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedTargetSubstInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedTargetSubst_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n m w param h hw
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedTargetSubst_step bound ih s n m w param h hw
      · exact ih p hlt s n m w param h hw
  exact hall (p+1) p (lt_add_one p) s n m w param h hw

#print axioms supportedTargetSubst_graph
#print axioms supportedTargetSubst_invariant
#print axioms supportedTargetSubst_step
#print axioms formulaSyntax_supported_targetSubst
end M6.PA.NumericPAeqFormula

