module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermCoverage
public import M6PA.Calibration.NumericPAeqTermFreeSupportLaws
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SupportedTermCovered (s n param t : V) : Prop :=
  ParametersValid s n param ∧ IsSemiterm Presentation.language s t ∧ FreeSupported (len (nth param 1)) t
noncomputable def supportedCoverageGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s n param t. ∃ b f z k, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧ !lenDef k f ∧
    !((isSemitermVec language).sigma) s n b ∧ !((isSemitermVec language).sigma) k n f ∧
    !((isSemiterm language).sigma) n z ∧ !((isSemiterm Presentation.language).sigma) s t ∧ !freeSupportedGraph k t”
theorem supportedCoverage_graph (s n param t : V) : supportedCoverageGraph.val.Evalb ![s,n,param,t] ↔ SupportedTermCovered s n param t := by
  simp [supportedCoverageGraph,freeSupported_graph,SupportedTermCovered,ParametersValid,Matrix.comp_vecCons'',and_assoc]

theorem supported_coverage_child {s n param t u : V} (h : SupportedTermCovered s n param t)
    (hu : IsSemiterm Presentation.language s u) (hs : FreeSupported (len (nth param 1)) u) :
    SupportedTermCovered s (n+1) (childParameters param) u := by
  refine ⟨childParameters_valid h.1,hu,?_⟩
  simp only [childParameters,parameters_free]
  rw [shiftTerms_length h.1.2.1]
  exact hs

theorem supported_coverage_binary_child {s n param t u i : V} (h : SupportedTermCovered s n param t)
    (hu : IsSemiterm Presentation.language s u) (hs : FreeSupported (len (nth param 1)) u) (hi : i<2) :
    SupportedTermCovered s ((n+1)+1) (binaryParameters param i) u := by
  refine ⟨binaryParameters_valid h.1 hi,hu,?_⟩
  simp only [binaryParameters,parameters_free]
  rw [shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)]
  exact hs

theorem supported_coverage_of_code {s n param t : V} (h : TermCovered s n param t) :
    SupportedTermCovered s n param t := ⟨h.1,h.2.1,freeSupported_of_code h.2.1.isUTerm h.2.2⟩
#print axioms supported_coverage_of_code
#print axioms supportedCoverage_graph
#print axioms supported_coverage_child
#print axioms supported_coverage_binary_child
end M6.PA.NumericPAeqTerm

