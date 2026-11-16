module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedSourceShiftAtoms
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedSourceShiftGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param x p. ∃ sp pp q sq, !prependFreeParametersGraph sp param x ∧
    !(shiftGraph Presentation.language) pp p ∧
    !formulaSyntaxGraph q param p ∧ !formulaSyntaxGraph sq sp pp ∧ sq=q”
theorem supportedSourceShift_graph (param x p : V) : supportedSourceShiftGraph.val.Evalb ![param,x,p] ↔
    formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p := by
  simp [supportedSourceShiftGraph,formulaSyntax_graph,prependFreeParameters_graph,Matrix.comp_vecCons'']
noncomputable def supportedSourceShiftInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param x, !supportedCoverageGraph s n param p →
    !((isSemiterm language).sigma) n x → !supportedSourceShiftGraph param x p”
theorem supportedSourceShift_invariant (bound : V) : supportedSourceShiftInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param x, SupportedFormulaCovered s n param p → IsSemiterm language n x →
      formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p := by
  simp [supportedSourceShiftInvariant,supportedCoverage_graph,supportedSourceShift_graph,Matrix.comp_vecCons'']
private theorem supportedSourceShift_step (p : V)
    (ih : ∀ q<p, ∀ s n param x, SupportedFormulaCovered s n param q → IsSemiterm language n x →
      formulaSyntax (prependFreeParameters param x) (shift Presentation.language q)=formulaSyntax param q) :
    ∀ s n param x, SupportedFormulaCovered s n param p → IsSemiterm language n x →
      formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p := by
  intro s n param x h hx
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · have ha := supported_coverage_rel h
    have hk := ha.1
    subst k
    rw [shift_rel hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr ht.termShiftVec.isUTerm,
      formulaSyntax_rel _ _ _ _ hr ht.isUTerm,atomCode_supported_sourceShift h.1 ha.2.2.1 ha.2.2.2 hx]
  · have ha := supported_coverage_nrel h
    have hk := ha.1
    subst k
    rw [shift_nrel hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr ht.termShiftVec.isUTerm,
      formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,atomCode_supported_sourceShift h.1 ha.2.2.1 ha.2.2.2 hx]
  · simp only [shift_verum,formulaSyntax_verum]
  · simp only [shift_falsum,formulaSyntax_falsum]
  · have hc := supported_coverage_and h
    rw [shift_and hp.isUFormula hq.isUFormula,
      formulaSyntax_and _ _ _ hp.shift.isUFormula hq.shift.isUFormula,
      formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_K!_left p q) s n param x hc.1 hx,ih q (lt_K!_right p q) s n param x hc.2 hx]
  · have hc := supported_coverage_or h
    rw [shift_or hp.isUFormula hq.isUFormula,
      formulaSyntax_or _ _ _ hp.shift.isUFormula hq.shift.isUFormula,
      formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_or_left p q) s n param x hc.1 hx,ih q (lt_or_right p q) s n param x hc.2 hx]
  · have hc := supported_coverage_all h
    rw [shift_all hp.isUFormula,formulaSyntax_all _ _ hp.shift.isUFormula,
      formulaSyntax_all _ _ hp.isUFormula,prependFreeParameters_binder h.1 hx,
      ih p (lt_forall p) (s+1) (n+1) _ _ hc hx.termBShift]
  · have hc := supported_coverage_exs h
    rw [shift_exs hp.isUFormula,formulaSyntax_exs _ _ hp.shift.isUFormula,
      formulaSyntax_exs _ _ hp.isUFormula,prependFreeParameters_binder h.1 hx,
      ih p (lt_exists p) (s+1) (n+1) _ _ hc hx.termBShift]
attribute [local irreducible] supportedSourceShiftInvariant
theorem formulaSyntax_supported_sourceShift {s n param p x : V} (h : SupportedFormulaCovered s n param p) (hx : IsSemiterm language n x) :
    formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param x, SupportedFormulaCovered s n param p → IsSemiterm language n x →
      formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param x, SupportedFormulaCovered s n param p → IsSemiterm language n x →
        formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)=formulaSyntax param p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedSourceShiftInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedSourceShift_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param x h hx
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedSourceShift_step bound ih s n param x h hx
      · exact ih p hlt s n param x h hx
  exact hall (p+1) p (lt_add_one p) s n param x h hx

theorem formulaSyntax_supported_sourceShift_parameters {s n b f p x:V}
    (h:SupportedFormulaCovered s n (parameters b f) p) (hx:IsSemiterm language n x):
    formulaSyntax (parameters b (x∷f)) (shift Presentation.language p)=formulaSyntax (parameters b f) p := by
  simpa [prependFreeParameters] using formulaSyntax_supported_sourceShift h hx

theorem formulaSyntax_supported_sourceShift_isSemiformula {s n param p x:V}
    (h:SupportedFormulaCovered s n param p) (hx:IsSemiterm language n x):
    IsSemiformula language n (formulaSyntax (prependFreeParameters param x) (shift Presentation.language p)) := by
  rw [formulaSyntax_supported_sourceShift h hx]
  exact formulaSyntax_supported_isSemiformula h

#print axioms formulaSyntax_supported_sourceShift_parameters
#print axioms formulaSyntax_supported_sourceShift_isSemiformula
#print axioms supportedSourceShift_graph
#print axioms supportedSourceShift_invariant
#print axioms supportedSourceShift_step
#print axioms formulaSyntax_supported_sourceShift
end M6.PA.NumericPAeqFormula

