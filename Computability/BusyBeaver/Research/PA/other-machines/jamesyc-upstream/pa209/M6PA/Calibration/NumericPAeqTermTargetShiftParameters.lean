module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetShiftTemplates
public import M6PA.Calibration.NumericPAeqTermChildren
@[expose] public section

namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def targetShiftTerms (v : V) : V := termShiftVec language (len v) v
noncomputable def targetShiftTermsGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out v. ∃ k, !lenDef k v ∧ !(termShiftVecGraph language) out k v”
theorem targetShiftTerms_graph (out v : V) :
    targetShiftTermsGraph.val.Evalb ![out,v] ↔ out=targetShiftTerms v := by
  simp [targetShiftTermsGraph,targetShiftTerms]
instance targetShiftTerms_defined : 𝚺ᴬ₁-Function₁ (targetShiftTerms : V → V) via targetShiftTermsGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! targetShiftTerms_graph (v 0) (v 1)

theorem targetShiftTerms_length {k n v : V} (h : IsSemitermVec language k n v) :
    len (targetShiftTerms v)=k := by simp [targetShiftTerms,h.lh,h.isUTerm]
theorem targetShiftTerms_nth {k n v i : V} (h : IsSemitermVec language k n v) (hi : i<k) :
    nth (targetShiftTerms v) i=termShift language (nth v i) := by
  simp [targetShiftTerms,h.lh,nth_termShiftVec h.isUTerm hi]
theorem targetShiftTerms_valid {k n v : V} (h : IsSemitermVec language k n v) :
    IsSemitermVec language k n (targetShiftTerms v) := by
  simpa [targetShiftTerms,h.lh] using h.termShiftVec

theorem targetShiftTerms_shiftTerms {k n v : V} (h : IsSemitermVec language k n v) :
    targetShiftTerms (shiftTerms v)=shiftTerms (targetShiftTerms v) := by
  apply nth_ext' k
    (targetShiftTerms_length (shiftTerms_isSemitermVec h))
    (shiftTerms_length (targetShiftTerms_valid h))
  intro i hi
  rw [targetShiftTerms_nth (shiftTerms_isSemitermVec h) hi, shiftTerms_nth h hi,
    shiftTerms_nth (targetShiftTerms_valid h) hi, targetShiftTerms_nth h hi]
  exact (termBShift_termShift (h.nth hi)).symm

noncomputable def targetShiftParameters (param : V) : V :=
  parameters (targetShiftTerms (nth param 0)) (targetShiftTerms (nth param 1)) (termShift language (nth param 2))
noncomputable def targetShiftParametersGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f z bs fs zs,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !targetShiftTermsGraph bs b ∧ !targetShiftTermsGraph fs f ∧
    !(termShiftGraph language) zs z ∧ !parametersGraph out bs fs zs”
theorem targetShiftParameters_graph (out param : V) :
    targetShiftParametersGraph.val.Evalb ![out,param] ↔ out=targetShiftParameters param := by
  simp [targetShiftParametersGraph,targetShiftParameters,targetShiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance targetShiftParameters_defined : 𝚺ᴬ₁-Function₁ (targetShiftParameters : V → V) via targetShiftParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! targetShiftParameters_graph (v 0) (v 1)

theorem targetShiftParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid s n (targetShiftParameters param) := by
  simp only [ParametersValid,targetShiftParameters,parameters_bound,parameters_free,parameters_result]
  exact ⟨targetShiftTerms_valid h.1, by simpa [targetShiftTerms_length h.2.1] using targetShiftTerms_valid h.2.1,h.2.2.termShift⟩

theorem targetShiftParameters_child {s n param : V} (h : ParametersValid s n param) :
    targetShiftParameters (childParameters param)=childParameters (targetShiftParameters param) := by
  simp only [targetShiftParameters,childParameters,parameters_bound,parameters_free,parameters_result,
    targetShiftTerms_shiftTerms h.1,targetShiftTerms_shiftTerms h.2.1,termShift_bvar]

theorem targetShiftParameters_binary {s n param i : V} (h : ParametersValid s n param) :
    targetShiftParameters (binaryParameters param i)=binaryParameters (targetShiftParameters param) i := by
  simp only [targetShiftParameters,binaryParameters,parameters_bound,parameters_free,parameters_result,
    targetShiftTerms_shiftTerms (shiftTerms_isSemitermVec h.1),targetShiftTerms_shiftTerms (shiftTerms_isSemitermVec h.2.1),
    targetShiftTerms_shiftTerms h.1,targetShiftTerms_shiftTerms h.2.1,termShift_bvar]

#print axioms targetShiftTerms_graph
#print axioms targetShiftTerms_defined
#print axioms targetShiftTerms_length
#print axioms targetShiftTerms_nth
#print axioms targetShiftTerms_valid
#print axioms targetShiftTerms_shiftTerms
#print axioms targetShiftParameters_graph
#print axioms targetShiftParameters_defined
#print axioms targetShiftParameters_valid
#print axioms targetShiftParameters_child
#print axioms targetShiftParameters_binary
end M6.PA.NumericPAeqTerm

