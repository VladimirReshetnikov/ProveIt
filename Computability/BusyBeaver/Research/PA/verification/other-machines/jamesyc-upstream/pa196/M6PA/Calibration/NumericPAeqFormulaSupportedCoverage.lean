module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportLaws
@[expose] public section

/-! A conservative finite free-environment coverage invariant. The code bound
is sufficient, not necessary; existence of a sufficiently long environment is
not assumed here. All source and target context arities are explicit. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SupportedFormulaCovered (s n param p : V) : Prop :=
  ParametersValid s n param ∧ IsSemiformula Presentation.language s p ∧ FreeSupported (len (nth param 1)) p
noncomputable def supportedCoverageGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s n param p. ∃ b f k, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !lenDef k f ∧
    !((isSemitermVec language).sigma) s n b ∧ !((isSemitermVec language).sigma) k n f ∧
    !((isSemiformula Presentation.language).sigma) s p ∧ !freeSupportedGraph k p”
theorem supportedCoverage_graph (s n param p : V) :
    supportedCoverageGraph.val.Evalb ![s,n,param,p] ↔ SupportedFormulaCovered s n param p := by
  simp [supportedCoverageGraph,freeSupported_graph,SupportedFormulaCovered,ParametersValid,Matrix.comp_vecCons'',and_assoc]

theorem supported_coverage_all {s n param p : V} (h : SupportedFormulaCovered s n param (qqAll p)) :
    SupportedFormulaCovered (s+1) (n+1) (binderParameters param) p := by
  refine ⟨binderParameters_valid h.1,IsSemiformula.all.mp h.2.1,?_⟩
  have hf := NumericPAeqTerm.shiftTerms_length h.1.2
  simp only [binderParameters,parameters_free]
  rw [hf]
  exact (freeSupported_all (IsSemiformula.all.mp h.2.1).isUFormula).mp h.2.2

theorem supported_coverage_exs {s n param p : V} (h : SupportedFormulaCovered s n param (qqExs p)) :
    SupportedFormulaCovered (s+1) (n+1) (binderParameters param) p := by
  refine ⟨binderParameters_valid h.1,IsSemiformula.exs.mp h.2.1,?_⟩
  have hf := NumericPAeqTerm.shiftTerms_length h.1.2
  simp only [binderParameters,parameters_free]
  rw [hf]
  exact (freeSupported_exs (IsSemiformula.exs.mp h.2.1).isUFormula).mp h.2.2

theorem supported_coverage_and {s n param p q : V} (h : SupportedFormulaCovered s n param (qqAnd p q)) :
    SupportedFormulaCovered s n param p ∧ SupportedFormulaCovered s n param q := by
  have hpq := IsSemiformula.and.mp h.2.1
  exact ⟨⟨h.1,hpq.1,((freeSupported_and hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2).1⟩,
    ⟨h.1,hpq.2,((freeSupported_and hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2).2⟩⟩
theorem supported_coverage_or {s n param p q : V} (h : SupportedFormulaCovered s n param (qqOr p q)) :
    SupportedFormulaCovered s n param p ∧ SupportedFormulaCovered s n param q := by
  have hpq := IsSemiformula.or.mp h.2.1
  exact ⟨⟨h.1,hpq.1,((freeSupported_or hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2).1⟩,
    ⟨h.1,hpq.2,((freeSupported_or hpq.1.isUFormula hpq.2.isUFormula).mp h.2.2).2⟩⟩

theorem supported_coverage_rel {s n param k r ts : V} (h : SupportedFormulaCovered s n param (qqRel k r ts)) :
    k=2 ∧ r=0 ∧ IsSemitermVec Presentation.language 2 s ts ∧
    (∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) := by
  obtain ⟨hr,ht⟩ := IsSemiformula.rel.mp h.2.1
  obtain ⟨hk,htag⟩ := (Presentation.source_relations k r).mp hr
  subst k
  refine ⟨rfl,htag,ht,?_⟩
  intro i hi
  exact (freeSupported_rel hr ht.isUTerm).mp h.2.2 i hi

theorem supported_coverage_nrel {s n param k r ts : V} (h : SupportedFormulaCovered s n param (qqNRel k r ts)) :
    k=2 ∧ r=0 ∧ IsSemitermVec Presentation.language 2 s ts ∧
    (∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) := by
  obtain ⟨hr,ht⟩ := IsSemiformula.nrel.mp h.2.1
  obtain ⟨hk,htag⟩ := (Presentation.source_relations k r).mp hr
  subst k
  refine ⟨rfl,htag,ht,?_⟩
  intro i hi
  exact (freeSupported_nrel hr ht.isUTerm).mp h.2.2 i hi

theorem supported_coverage_of_code {s n param p : V} (h : FormulaCovered s n param p) :
    SupportedFormulaCovered s n param p := ⟨h.1,h.2.1,freeSupported_of_code h.2.1.isUFormula h.2.2⟩
#print axioms supportedCoverage_graph
#print axioms supported_coverage_all
#print axioms supported_coverage_exs
#print axioms supported_coverage_and
#print axioms supported_coverage_or
#print axioms supported_coverage_rel
#print axioms supported_coverage_nrel
end M6.PA.NumericPAeqFormula

