module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFunction
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def TermCovered (s n param t : V) : Prop :=
  ParametersValid s n param ∧ IsSemiterm Presentation.language s t ∧ t≤len (nth param 1)
noncomputable def coverageGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “s n param t. ∃ b f z k, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧ !lenDef k f ∧
    !((isSemitermVec language).sigma) s n b ∧ !((isSemitermVec language).sigma) k n f ∧
    !((isSemiterm language).sigma) n z ∧ !((isSemiterm Presentation.language).sigma) s t ∧ t≤k”
theorem coverage_graph (s n param t : V) : coverageGraph.val.Evalb ![s,n,param,t] ↔ TermCovered s n param t := by
  simp [coverageGraph,TermCovered,ParametersValid,Matrix.comp_vecCons'',and_assoc]

theorem coverage_child {s n param t u : V} (h : TermCovered s n param t)
    (hu : IsSemiterm Presentation.language s u) (hr : u<t) :
    TermCovered s (n+1) (childParameters param) u := by
  refine ⟨childParameters_valid h.1,hu,?_⟩
  simp only [childParameters,parameters_free]
  rw [shiftTerms_length h.1.2.1]
  exact le_trans hr.le h.2.2

theorem coverage_binary_child {s n param t u i : V} (h : TermCovered s n param t)
    (hu : IsSemiterm Presentation.language s u) (hr : u<t) (hi : i<2) :
    TermCovered s ((n+1)+1) (binaryParameters param i) u := by
  refine ⟨binaryParameters_valid h.1 hi,hu,?_⟩
  simp only [binaryParameters,parameters_free]
  rw [shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)]
  exact le_trans hr.le h.2.2

#print axioms coverage_graph
#print axioms coverage_child
#print axioms coverage_binary_child
end M6.PA.NumericPAeqTerm

