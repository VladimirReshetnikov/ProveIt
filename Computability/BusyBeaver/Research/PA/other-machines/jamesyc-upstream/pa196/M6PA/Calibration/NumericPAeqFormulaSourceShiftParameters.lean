module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
public import M6PA.Calibration.NumericPAeqTermSourceShiftParameters
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def prependFreeParameters (param x : V) : V :=
  parameters (nth param 0) (x ∷ nth param 1)
noncomputable def prependFreeParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param x. ∃ b f xf, !nthDef b param 0 ∧ !nthDef f param 1 ∧
    !adjoinDef xf x f ∧ !parametersGraph out b xf”
theorem prependFreeParameters_graph (out param x : V) :
    prependFreeParametersGraph.val.Evalb ![out,param,x] ↔ out=prependFreeParameters param x := by
  simp [prependFreeParametersGraph,prependFreeParameters,parameters_graph,Matrix.comp_vecCons'']
instance prependFreeParameters_defined : 𝚺ᴬ₁-Function₂ (prependFreeParameters : V → V → V) via prependFreeParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! prependFreeParameters_graph (v 0) (v 1) (v 2)
theorem prependFreeParameters_valid {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) : ParametersValid s n (prependFreeParameters param x) := by
  simp only [ParametersValid,prependFreeParameters,parameters_bound,parameters_free]
  exact ⟨h.1,by simp [hx,h.2]⟩
theorem prependFreeParameters_equality {s n param x i : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    equalityTermParameters (prependFreeParameters param x) i=
      NumericPAeqTerm.prependFreeParameters (equalityTermParameters param i)
        (termBShift language (termBShift language x)) := by
  simp only [equalityTermParameters,prependFreeParameters,NumericPAeqTerm.prependFreeParameters,
    parameters_bound,parameters_free,NumericPAeqTerm.parameters_bound,NumericPAeqTerm.parameters_free,
    NumericPAeqTerm.parameters_result,NumericPAeqTerm.shiftTerms_adjoin h.2 hx,
    NumericPAeqTerm.shiftTerms_adjoin (NumericPAeqTerm.shiftTerms_isSemitermVec h.2) hx.termBShift]
theorem prependFreeParameters_binder {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    binderParameters (prependFreeParameters param x)=
      prependFreeParameters (binderParameters param) (termBShift language x) := by
  simp only [binderParameters,prependFreeParameters,parameters_bound,parameters_free,
    NumericPAeqTerm.shiftTerms_adjoin h.2 hx]
#print axioms prependFreeParameters_defined
#print axioms prependFreeParameters_valid
#print axioms prependFreeParameters_equality
#print axioms prependFreeParameters_binder
end M6.PA.NumericPAeqFormula

