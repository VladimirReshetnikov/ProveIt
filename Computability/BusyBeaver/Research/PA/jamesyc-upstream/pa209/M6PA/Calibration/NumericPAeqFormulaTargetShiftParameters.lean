module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaCoverage
public import M6PA.Calibration.NumericPAeqTermTargetShiftParameters
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm (targetShiftTerms targetShiftTermsGraph targetShiftTerms_graph
 targetShiftTerms_valid targetShiftTerms_length targetShiftTerms_shiftTerms shiftTerms shiftTerms_isSemitermVec)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def targetShiftParameters (param : V) : V :=
  parameters (targetShiftTerms (nth param 0)) (targetShiftTerms (nth param 1))
noncomputable def targetShiftParametersGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f bs fs, !nthDef b param 0 ∧ !nthDef f param 1 ∧
    !targetShiftTermsGraph bs b ∧ !targetShiftTermsGraph fs f ∧ !parametersGraph out bs fs”
theorem targetShiftParameters_graph (out param : V) :
    targetShiftParametersGraph.val.Evalb ![out,param] ↔ out=targetShiftParameters param := by
  simp [targetShiftParametersGraph,targetShiftParameters,targetShiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance targetShiftParameters_defined : 𝚺ᴬ₁-Function₁ (targetShiftParameters : V → V) via targetShiftParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! targetShiftParameters_graph (v 0) (v 1)
theorem targetShiftParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid s n (targetShiftParameters param) := by
  simp only [ParametersValid,targetShiftParameters,parameters_bound,parameters_free]
  exact ⟨targetShiftTerms_valid h.1,by simpa [targetShiftTerms_length h.2] using targetShiftTerms_valid h.2⟩
theorem targetShiftParameters_covered {s n param p : V} (h : FormulaCovered s n param p) :
    FormulaCovered s n (targetShiftParameters param) p := by
  exact ⟨targetShiftParameters_valid h.1,h.2.1,by simpa [targetShiftParameters,targetShiftTerms_length h.1.2] using h.2.2⟩
theorem targetShiftParameters_equality {s n param i : V} (h : ParametersValid s n param) :
    NumericPAeqTerm.targetShiftParameters (equalityTermParameters param i)=
      equalityTermParameters (targetShiftParameters param) i := by
  simp only [NumericPAeqTerm.targetShiftParameters,equalityTermParameters,targetShiftParameters,
    NumericPAeqTerm.parameters_bound,NumericPAeqTerm.parameters_free,NumericPAeqTerm.parameters_result,
    parameters_bound,parameters_free,
    targetShiftTerms_shiftTerms (shiftTerms_isSemitermVec h.1),
    targetShiftTerms_shiftTerms (shiftTerms_isSemitermVec h.2),
    targetShiftTerms_shiftTerms h.1,targetShiftTerms_shiftTerms h.2,termShift_bvar]
theorem targetShiftTerms_adjoin {k n v a : V} (hv : IsSemitermVec language k n v)
    (ha : IsSemiterm language n a) :
    targetShiftTerms (a ∷ v)=termShift language a ∷ targetShiftTerms v := by
  simp [NumericPAeqTerm.targetShiftTerms,hv.lh,termShiftVec_cons ha.isUTerm hv.isUTerm]
theorem targetShiftParameters_binder {s n param : V} (h : ParametersValid s n param) :
    targetShiftParameters (binderParameters param)=binderParameters (targetShiftParameters param) := by
  simp only [targetShiftParameters,binderParameters,parameters_bound,parameters_free]
  rw [targetShiftTerms_adjoin (shiftTerms_isSemitermVec h.1) (by simp),termShift_bvar,
    targetShiftTerms_shiftTerms h.1,targetShiftTerms_shiftTerms h.2]
#print axioms targetShiftParameters_defined
#print axioms targetShiftParameters_valid
#print axioms targetShiftParameters_covered
#print axioms targetShiftParameters_equality
#print axioms targetShiftParameters_binder
end M6.PA.NumericPAeqFormula

