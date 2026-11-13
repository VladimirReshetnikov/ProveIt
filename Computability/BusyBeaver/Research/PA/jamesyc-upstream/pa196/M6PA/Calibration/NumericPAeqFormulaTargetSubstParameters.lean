module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedCoverage
public import M6PA.Calibration.NumericPAeqTermTargetSubstParameters
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalPredicateTemplate (substTerms substTermsGraph substTerms_graph substTerms_length substTerms_valid)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def targetSubstParameters (w param : V) : V :=
  parameters (substTerms w (nth param 0)) (substTerms w (nth param 1))
attribute [local irreducible] substTermsGraph
noncomputable def targetSubstParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out w param. ∃ b f bs fs, !nthDef b param 0 ∧ !nthDef f param 1 ∧
    !substTermsGraph bs w b ∧ !substTermsGraph fs w f ∧ !parametersGraph out bs fs”
theorem targetSubstParameters_graph (out w param : V) :
    targetSubstParametersGraph.val.Evalb ![out,w,param] ↔ out=targetSubstParameters w param := by
  simp [targetSubstParametersGraph,targetSubstParameters,substTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance targetSubstParameters_defined : 𝚺ᴬ₁-Function₂ (targetSubstParameters : V→V→V) via targetSubstParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! targetSubstParameters_graph (v 0) (v 1) (v 2)
theorem targetSubstParameters_valid {s n m param w : V} (h : ParametersValid s n param)
    (hw : IsSemitermVec language n m w) : ParametersValid s m (targetSubstParameters w param) := by
  simp only [ParametersValid,targetSubstParameters,parameters_bound,parameters_free]
  exact ⟨substTerms_valid h.1 hw,by simpa [substTerms_length h.2] using substTerms_valid h.2 hw⟩
theorem targetSubstParameters_supported_covered {s n m param w p : V} (h : SupportedFormulaCovered s n param p)
    (hw : IsSemitermVec language n m w) : SupportedFormulaCovered s m (targetSubstParameters w param) p :=
  ⟨targetSubstParameters_valid h.1 hw,h.2.1,by simpa [targetSubstParameters,substTerms_length h.1.2] using h.2.2⟩

theorem targetSubstParameters_binder {s n m param w : V} (h : ParametersValid s n param)
    (hw : IsSemitermVec language n m w) :
    targetSubstParameters (qVec language w) (binderParameters param)=binderParameters (targetSubstParameters w param) := by
  simp only [targetSubstParameters,binderParameters,parameters_bound,parameters_free]
  change parameters (substTerms (qVec language w) (RelationalPredicateTemplate.bindBound (nth param 0)))
    (substTerms (qVec language w) (RelationalPredicateTemplate.bindFree (nth param 1))) = _
  rw [RelationalPredicateTemplate.bindBound_subst h.1 hw,RelationalPredicateTemplate.bindFree_subst h.2 hw]
  rfl

theorem targetSubstParameters_equality {s n m param w i : V} (h : ParametersValid s n param)
    (hw : IsSemitermVec language n m w) (hi : i<2) :
    NumericPAeqTerm.targetSubstParameters (qVec language (qVec language w)) (equalityTermParameters param i)=
      equalityTermParameters (targetSubstParameters w param) i := by
  simp only [NumericPAeqTerm.targetSubstParameters,equalityTermParameters,targetSubstParameters,
    NumericPAeqTerm.parameters_bound,NumericPAeqTerm.parameters_free,NumericPAeqTerm.parameters_result,
    parameters_bound,parameters_free,
    NumericPAeqTerm.substTerms_shiftTerms (NumericPAeqTerm.shiftTerms_isSemitermVec h.1) hw.qVec,
    NumericPAeqTerm.substTerms_shiftTerms (NumericPAeqTerm.shiftTerms_isSemitermVec h.2) hw.qVec,
    NumericPAeqTerm.substTerms_shiftTerms h.1 hw,NumericPAeqTerm.substTerms_shiftTerms h.2 hw]
  have hh : termSubst language (qVec language (qVec language w)) (qqBvar i)=qqBvar i := by
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl|rfl
    · simp [qVec]
    · simpa [qVec] using substs_qVec_bShift (show IsSemiterm language (n+1) (qqBvar (0:V)) by simp) hw.qVec
  rw [hh]
#print axioms targetSubstParameters_defined
#print axioms targetSubstParameters_valid
#print axioms targetSubstParameters_binder
#print axioms targetSubstParameters_equality
end M6.PA.NumericPAeqFormula

