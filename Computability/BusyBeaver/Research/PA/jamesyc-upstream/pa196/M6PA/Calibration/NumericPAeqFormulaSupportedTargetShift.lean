module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetShiftAtoms
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedTargetShiftGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “param p. ∃ sp q sq tq, !targetShiftParametersGraph sp param ∧
    !formulaSyntaxGraph q param p ∧ !formulaSyntaxGraph sq sp p ∧
    !(shiftGraph language) tq q ∧ tq=sq”
theorem supportedTargetShift_graph (param p : V) : supportedTargetShiftGraph.val.Evalb ![param,p] ↔
    shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p := by
  simp [supportedTargetShiftGraph,formulaSyntax_graph,targetShiftParameters_graph,Matrix.comp_vecCons'']
noncomputable def supportedTargetShiftInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param, !supportedCoverageGraph s n param p → !supportedTargetShiftGraph param p”
theorem supportedTargetShift_invariant (bound : V) : supportedTargetShiftInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
      shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p := by
  simp [supportedTargetShiftInvariant,supportedCoverage_graph,supportedTargetShift_graph,Matrix.comp_vecCons'']
private theorem supportedTargetShift_step (p : V)
    (ih : ∀ q<p, ∀ s n param, SupportedFormulaCovered s n param q →
      shift language (formulaSyntax param q)=formulaSyntax (targetShiftParameters param) q) :
    ∀ s n param, SupportedFormulaCovered s n param p →
      shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p := by
  intro s n param h
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · have ha := supported_coverage_rel h
    rw [formulaSyntax_rel _ _ _ _ hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr ht.isUTerm,
      atomCode_supported_targetShift h.1 ha.2.2.1 ha.2.2.2]
  · have ha := supported_coverage_nrel h
    rw [formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,
      shift_neg (atomCode_supported_isSemiformula (k:=k) (r:=r) h.1 ha.2.2.1 ha.2.2.2),
      atomCode_supported_targetShift h.1 ha.2.2.1 ha.2.2.2]
  · simp only [formulaSyntax_verum,shift_verum]
  · simp only [formulaSyntax_falsum,shift_falsum]
  · have hc := supported_coverage_and h
    rw [formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      shift_and (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_K!_left p q) s n param hc.1,ih q (lt_K!_right p q) s n param hc.2]
  · have hc := supported_coverage_or h
    rw [formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      shift_or (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_or_left p q) s n param hc.1,ih q (lt_or_right p q) s n param hc.2]
  · have hc := supported_coverage_all h
    rw [formulaSyntax_all _ _ hp.isUFormula,formulaSyntax_all _ _ hp.isUFormula,
      guardedAllCode_targetShift (formulaSyntax_supported_isSemiformula hc).isUFormula,
      ih p (lt_forall p) (s+1) (n+1) _ hc,targetShiftParameters_binder h.1]
  · have hc := supported_coverage_exs h
    rw [formulaSyntax_exs _ _ hp.isUFormula,formulaSyntax_exs _ _ hp.isUFormula,
      guardedExsCode_targetShift (formulaSyntax_supported_isSemiformula hc).isUFormula,
      ih p (lt_exists p) (s+1) (n+1) _ hc,targetShiftParameters_binder h.1]
attribute [local irreducible] supportedTargetShiftInvariant
theorem formulaSyntax_supported_targetShift {s n param p : V} (h : SupportedFormulaCovered s n param p) :
    shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
      shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
        shift language (formulaSyntax param p)=formulaSyntax (targetShiftParameters param) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedTargetShiftInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedTargetShift_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedTargetShift_step bound ih s n param h
      · exact ih p hlt s n param h
  exact hall (p+1) p (lt_add_one p) s n param h

#print axioms supportedTargetShift_graph
#print axioms supportedTargetShift_invariant
#print axioms supportedTargetShift_step
#print axioms formulaSyntax_supported_targetShift
end M6.PA.NumericPAeqFormula

