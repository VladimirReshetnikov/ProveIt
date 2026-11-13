module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceShiftParameters
@[expose] public section

/-! Prepending a target bound-environment entry compensates for source bound shift.
The free environment and result term are preserved. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prependBoundParameters (param x : V) : V :=
  parameters (x ∷ nth param 0) (nth param 1) (nth param 2)
noncomputable def prependBoundParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param x. ∃ b f z xb, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !adjoinDef xb x b ∧ !parametersGraph out xb f z”
theorem prependBoundParameters_graph (out param x : V) :
    prependBoundParametersGraph.val.Evalb ![out,param,x] ↔ out=prependBoundParameters param x := by
  simp [prependBoundParametersGraph,prependBoundParameters,parameters_graph,Matrix.comp_vecCons'']
instance prependBoundParameters_defined : 𝚺ᴬ₁-Function₂ (prependBoundParameters : V → V → V) via prependBoundParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! prependBoundParameters_graph (v 0) (v 1) (v 2)

theorem prependBoundParameters_valid {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) : ParametersValid (s+1) n (prependBoundParameters param x) := by
  simp only [ParametersValid,prependBoundParameters,parameters_bound,parameters_free,parameters_result]
  exact ⟨by simp [hx,h.1],h.2.1,h.2.2⟩

theorem childParameters_prependBound {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    childParameters (prependBoundParameters param x)=
      prependBoundParameters (childParameters param) (termBShift language x) := by
  simp only [childParameters,prependBoundParameters,parameters_bound,parameters_free,parameters_result,
    shiftTerms_adjoin h.1 hx]

theorem binaryParameters_prependBound {s n param x i : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    binaryParameters (prependBoundParameters param x) i=
      prependBoundParameters (binaryParameters param i) (termBShift language (termBShift language x)) := by
  simp only [binaryParameters,prependBoundParameters,parameters_bound,parameters_free,parameters_result,
    shiftTerms_adjoin h.1 hx,shiftTerms_adjoin (shiftTerms_isSemitermVec h.1) hx.termBShift]

#print axioms prependBoundParameters_graph
#print axioms prependBoundParameters_defined
#print axioms prependBoundParameters_valid
#print axioms childParameters_prependBound
#print axioms binaryParameters_prependBound
end M6.PA.NumericPAeqTerm
