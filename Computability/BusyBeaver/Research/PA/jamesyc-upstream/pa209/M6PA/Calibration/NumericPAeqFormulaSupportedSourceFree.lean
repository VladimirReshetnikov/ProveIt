module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSourceFreeCalibration
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
public import M6PA.Calibration.NumericPAeqFormulaSourceFreeArity
public import M6PA.Calibration.NumericPAeqFormulaSupportedSourceFreeAtoms
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedSourceFreeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “s param p. ∃ sp pp q sq, !sourceFreeParametersGraph sp s param ∧
    !formulaSourceFreeGraph pp s p ∧
    !formulaSyntaxGraph q param p ∧ !formulaSyntaxGraph sq sp pp ∧ sq=q”
theorem supportedSourceFree_graph (s param p : V) : supportedSourceFreeGraph.val.Evalb ![s,param,p] ↔
    formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p := by
  simp [supportedSourceFreeGraph,formulaSyntax_graph,sourceFreeParameters_graph,formulaSourceFree_graph,Matrix.comp_vecCons'']
noncomputable def supportedSourceFreeInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param, !supportedCoverageGraph (s+1) n param p → !supportedSourceFreeGraph s param p”
theorem supportedSourceFree_invariant (bound : V) : supportedSourceFreeInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param, SupportedFormulaCovered (s+1) n param p →
      formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p := by
  simp [supportedSourceFreeInvariant,supportedCoverage_graph,supportedSourceFree_graph,Matrix.comp_vecCons'']
private theorem supportedSourceFree_step (p : V)
    (ih : ∀ q<p, ∀ s n param, SupportedFormulaCovered (s+1) n param q →
      formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s q)=formulaSyntax param q) :
    ∀ s n param, SupportedFormulaCovered (s+1) n param p →
      formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p := by
  intro s n param h
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · have ha := supported_coverage_rel h
    have hk := ha.1
    subst k
    rw [formulaSourceFree_rel _ _ _ _ hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr (sourceFreeVec_isSemitermVec ht).isUTerm,
      formulaSyntax_rel _ _ _ _ hr ht.isUTerm,atomCode_supported_sourceFree h.1 ha.2.2.1 ha.2.2.2]
  · have ha := supported_coverage_nrel h
    have hk := ha.1
    subst k
    rw [formulaSourceFree_nrel _ _ _ _ hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr (sourceFreeVec_isSemitermVec ht).isUTerm,
      formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,atomCode_supported_sourceFree h.1 ha.2.2.1 ha.2.2.2]
  · simp only [formulaSourceFree_verum,formulaSyntax_verum]
  · simp only [formulaSourceFree_falsum,formulaSyntax_falsum]
  · have hc := supported_coverage_and h
    rw [formulaSourceFree_and _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_and _ _ _ (formulaSourceFree_isSemiformula hp).isUFormula (formulaSourceFree_isSemiformula hq).isUFormula,
      formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_K!_left p q) s n param hc.1,ih q (lt_K!_right p q) s n param hc.2]
  · have hc := supported_coverage_or h
    rw [formulaSourceFree_or _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_or _ _ _ (formulaSourceFree_isSemiformula hp).isUFormula (formulaSourceFree_isSemiformula hq).isUFormula,
      formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_or_left p q) s n param hc.1,ih q (lt_or_right p q) s n param hc.2]
  · have hc := supported_coverage_all h
    rw [formulaSourceFree_all _ _ hp.isUFormula,formulaSyntax_all _ _ (formulaSourceFree_isSemiformula hp).isUFormula,
      formulaSyntax_all _ _ hp.isUFormula,sourceFreeParameters_binder h.1,
      ih p (lt_forall p) (s+1) (n+1) _ hc]
  · have hc := supported_coverage_exs h
    rw [formulaSourceFree_exs _ _ hp.isUFormula,formulaSyntax_exs _ _ (formulaSourceFree_isSemiformula hp).isUFormula,
      formulaSyntax_exs _ _ hp.isUFormula,sourceFreeParameters_binder h.1,
      ih p (lt_exists p) (s+1) (n+1) _ hc]
attribute [local irreducible] supportedSourceFreeInvariant
theorem formulaSyntax_supported_sourceFree {s n param p : V} (h : SupportedFormulaCovered (s+1) n param p) :
    formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param, SupportedFormulaCovered (s+1) n param p →
      formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param, SupportedFormulaCovered (s+1) n param p →
        formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)=formulaSyntax param p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedSourceFreeInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedSourceFree_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedSourceFree_step bound ih s n param h
      · exact ih p hlt s n param h
  exact hall (p+1) p (lt_add_one p) s n param h

theorem formulaSyntax_supported_sourceFree_isSemiformula {s n param p : V}
    (h : SupportedFormulaCovered (s+1) n param p) :
    IsSemiformula language n (formulaSyntax (sourceFreeParameters s param) (formulaSourceFree s p)) := by
  rw [formulaSyntax_supported_sourceFree h]
  exact formulaSyntax_supported_isSemiformula h

theorem formulaSyntax_supported_free {n param p : V} (h : SupportedFormulaCovered 1 n param p) :
    formulaSyntax (sourceFreeParameters 0 param) (free Presentation.language p)=formulaSyntax param p := by
  rw [← formulaSourceFree_zero_eq_free h.2.1]
  exact formulaSyntax_supported_sourceFree (by simpa using h)

theorem formulaSyntax_supported_free_singleton {n a f p : V}
    (h : SupportedFormulaCovered 1 n (parameters (a∷0) f) p) :
    formulaSyntax (parameters 0 (a∷f)) (free Presentation.language p)=
      formulaSyntax (parameters (a∷0) f) p := by
  simpa [sourceFreeParameters,NumericPAeqTerm.dropLast_adjoin] using formulaSyntax_supported_free h

#print axioms supportedSourceFree_graph
#print axioms supportedSourceFree_invariant
#print axioms supportedSourceFree_step
#print axioms formulaSyntax_supported_sourceFree
#print axioms formulaSyntax_supported_sourceFree_isSemiformula
#print axioms formulaSyntax_supported_free
#print axioms formulaSyntax_supported_free_singleton
end M6.PA.NumericPAeqFormula

