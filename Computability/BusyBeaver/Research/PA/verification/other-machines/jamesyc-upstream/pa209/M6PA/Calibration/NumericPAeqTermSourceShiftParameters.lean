module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermChildren
@[expose] public section

/-! Prepending a target free-environment entry compensates for source free shift.
The bound environment and result term are preserved. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prependFreeParameters (param x : V) : V :=
  parameters (nth param 0) (x ∷ nth param 1) (nth param 2)
noncomputable def prependFreeParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out param x. ∃ b f z xf, !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !adjoinDef xf x f ∧ !parametersGraph out b xf z”
theorem prependFreeParameters_graph (out param x : V) :
    prependFreeParametersGraph.val.Evalb ![out,param,x] ↔ out=prependFreeParameters param x := by
  simp [prependFreeParametersGraph,prependFreeParameters,parameters_graph,Matrix.comp_vecCons'']
instance prependFreeParameters_defined : 𝚺ᴬ₁-Function₂ (prependFreeParameters : V → V → V) via prependFreeParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! prependFreeParameters_graph (v 0) (v 1) (v 2)

theorem prependFreeParameters_valid {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) : ParametersValid s n (prependFreeParameters param x) := by
  simp only [ParametersValid,prependFreeParameters,parameters_bound,parameters_free,parameters_result]
  exact ⟨h.1,by simp [hx,h.2.1],h.2.2⟩

theorem shiftTerms_adjoin {k n v x : V} (h : IsSemitermVec language k n v)
    (hx : IsSemiterm language n x) :
    shiftTerms (x∷v)=termBShift language x ∷ shiftTerms v := by
  simp [shiftTerms,h.lh,termBShiftVec_cons hx.isUTerm h.isUTerm]

theorem childParameters_prependFree {s n param x : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    childParameters (prependFreeParameters param x)=
      prependFreeParameters (childParameters param) (termBShift language x) := by
  simp only [childParameters,prependFreeParameters,parameters_bound,parameters_free,parameters_result,
    shiftTerms_adjoin h.2.1 hx]

theorem binaryParameters_prependFree {s n param x i : V} (h : ParametersValid s n param)
    (hx : IsSemiterm language n x) :
    binaryParameters (prependFreeParameters param x) i=
      prependFreeParameters (binaryParameters param i) (termBShift language (termBShift language x)) := by
  simp only [binaryParameters,prependFreeParameters,parameters_bound,parameters_free,parameters_result,
    shiftTerms_adjoin h.2.1 hx,shiftTerms_adjoin (shiftTerms_isSemitermVec h.2.1) hx.termBShift]

#print axioms prependFreeParameters_graph
#print axioms prependFreeParameters_defined
#print axioms prependFreeParameters_valid
#print axioms shiftTerms_adjoin
#print axioms childParameters_prependFree
#print axioms binaryParameters_prependFree
end M6.PA.NumericPAeqTerm

