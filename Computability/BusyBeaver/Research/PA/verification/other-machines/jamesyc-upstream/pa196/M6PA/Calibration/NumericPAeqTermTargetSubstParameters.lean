module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermChildren
public import M6PA.Calibration.RelationalPredicateTemplateSubstitutionBinders
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalPredicateTemplate (substTerms substTermsGraph substTerms_graph substTerms_length substTerms_nth substTerms_valid)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def targetSubstParameters (w param : V) : V :=
  parameters (substTerms w (nth param 0)) (substTerms w (nth param 1)) (termSubst language w (nth param 2))
attribute [local irreducible] substTermsGraph
noncomputable def targetSubstParametersGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out w param. ∃ b f z bs fs zs,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !substTermsGraph bs w b ∧ !substTermsGraph fs w f ∧
    !(termSubstGraph language) zs w z ∧ !parametersGraph out bs fs zs”
theorem targetSubstParameters_graph (out w param : V) :
    targetSubstParametersGraph.val.Evalb ![out,w,param] ↔ out=targetSubstParameters w param := by
  simp [targetSubstParametersGraph,targetSubstParameters,substTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance targetSubstParameters_defined : 𝚺ᴬ₁-Function₂ (targetSubstParameters : V→V→V) via targetSubstParametersGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! targetSubstParameters_graph (v 0) (v 1) (v 2)

theorem targetSubstParameters_valid {s n m w param : V} (h:ParametersValid s n param)
    (hw:IsSemitermVec language n m w) : ParametersValid s m (targetSubstParameters w param) := by
  simp only [ParametersValid,targetSubstParameters,parameters_bound,parameters_free,parameters_result]
  exact ⟨substTerms_valid h.1 hw,by simpa [substTerms_length h.2.1] using substTerms_valid h.2.1 hw,hw.termSubst h.2.2⟩

theorem substTerms_shiftTerms {k n m v w : V} (hv:IsSemitermVec language k n v)
    (hw:IsSemitermVec language n m w) :
    substTerms (qVec language w) (shiftTerms v)=shiftTerms (substTerms w v) :=
  RelationalPredicateTemplate.bindFree_subst hv hw

theorem targetSubstParameters_child {s n m w param : V} (h:ParametersValid s n param)
    (hw:IsSemitermVec language n m w) :
    targetSubstParameters (qVec language w) (childParameters param)=childParameters (targetSubstParameters w param) := by
  simp only [targetSubstParameters,childParameters,parameters_bound,parameters_free,parameters_result,
    substTerms_shiftTerms h.1 hw,substTerms_shiftTerms h.2.1 hw]
  simp [qVec]

theorem targetSubstParameters_binary {s n m w param i : V} (h:ParametersValid s n param)
    (hw:IsSemitermVec language n m w) (hi:i<2) :
    targetSubstParameters (qVec language (qVec language w)) (binaryParameters param i)=
      binaryParameters (targetSubstParameters w param) i := by
  simp only [targetSubstParameters,binaryParameters,parameters_bound,parameters_free,parameters_result,
    substTerms_shiftTerms (shiftTerms_isSemitermVec h.1) hw.qVec,
    substTerms_shiftTerms (shiftTerms_isSemitermVec h.2.1) hw.qVec,
    substTerms_shiftTerms h.1 hw,substTerms_shiftTerms h.2.1 hw]
  have ht : termSubst language (qVec language (qVec language w)) (qqBvar i)=qqBvar i := by
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl|rfl
    · simp [qVec]
    · simpa [qVec] using (substs_qVec_bShift
        (show IsSemiterm language (n+1) (qqBvar (0:V)) by simp) hw.qVec)
  rw [ht]

#print axioms targetSubstParameters_graph
#print axioms targetSubstParameters_defined
#print axioms targetSubstParameters_valid
#print axioms targetSubstParameters_child
#print axioms targetSubstParameters_binary
end M6.PA.NumericPAeqTerm

