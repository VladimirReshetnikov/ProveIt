module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentReserve
public import M6PA.Calibration.FoundationRelationalSequentClosedEnvironment
public import M6PA.Calibration.FoundationRelationalSequentEnvironmentExistence
@[expose] public section

/-! Joint parameter relocation for shift-fixed formulas at bound context zero.
The intermediate model-length zero environment and maximum reserve satisfy
all coverage guards explicitly; no standardness of parameters is assumed. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem coverage_zero_environment {p f lo z : V} (h : FormulaCovered 0 f lo z p) :
    FormulaCovered 0 (zeroEnvironment p) lo z p := by
  refine ⟨⟨?_,h.1.2⟩,h.2.1,?_⟩
  · refine ⟨h.1.1.1,h.1.1.2.1,?_,?_⟩
    · intro i hi
      simp at hi
    · intro i hi
      have hz := zeroEnvironment_properties (V:=V) p
      rw [hz.1] at hi
      rw [hz.2 i hi]
      exact h.1.1.1
  · exact (zeroEnvironment_properties p).1.ge

theorem coverage_reserve_raise {p b f lo z other : V}
    (h : FormulaCovered b f lo z p) (hz : z≤other) : FormulaCovered b f lo other p :=
  ⟨⟨⟨h.1.1.1,le_trans h.1.1.2.1 hz,h.1.1.2.2⟩,le_trans h.1.2 hz⟩,h.2⟩

theorem closed_formula_parameter_certificates (p f lo z g otherLo otherZ : V)
    (hc : Bootstrapping.shift language p=p)
    (hl : FormulaCovered 0 f lo z p) (hr : FormulaCovered 0 g otherLo otherZ p) :
    ∃ forward backward, BiCertificates forward backward
      (translate (parameters 0 f lo z) p) (translate (parameters 0 g otherLo otherZ) p) := by
  let zero := zeroEnvironment p
  let reserve := max z otherZ
  have hleft : FormulaCovered 0 zero lo z p := coverage_zero_environment hl
  have hright : FormulaCovered 0 zero otherLo otherZ p := coverage_zero_environment hr
  have hleft' : FormulaCovered 0 zero lo reserve p := coverage_reserve_raise hleft (le_max_left _ _)
  have hright' : FormulaCovered 0 zero otherLo reserve p := coverage_reserve_raise hright (le_max_right _ _)
  obtain ⟨c,d,hc',hd⟩ := formula_reserve_certificates p 0 zero lo z reserve hleft hleft'
  obtain ⟨e,j,he,hj⟩ := formula_allocator_certificates p 0 zero lo otherLo reserve hleft' hright'
  obtain ⟨k,l,hk,hl'⟩ := formula_reserve_certificates p 0 zero otherLo otherZ reserve hright hright'
  let left : BiWitness (translate (parameters 0 zero lo z) p)
    (translate (parameters 0 zero lo reserve) p) := ⟨⟨c,hc'⟩,⟨d,hd⟩⟩
  let middle : BiWitness (translate (parameters 0 zero lo reserve) p)
    (translate (parameters 0 zero otherLo reserve) p) := ⟨⟨e,he⟩,⟨j,hj⟩⟩
  let right : BiWitness (translate (parameters 0 zero otherLo otherZ) p)
    (translate (parameters 0 zero otherLo reserve) p) := ⟨⟨k,hk⟩,⟨l,hl'⟩⟩
  rw [translate_closed_free_environments p 0 f zero lo z hl.2.1.isUFormula hc,
    translate_closed_free_environments p 0 g zero otherLo otherZ hr.2.1.isUFormula hc]
  exact ⟨_,_,((left.trans middle).trans right.symm).accepted⟩

attribute [local irreducible] coverageGraph parametersGraph translateGraph biGraph shiftGraph
noncomputable def closedParameterSentence : ArithmeticSentence :=
  “∀ p f lo z g otherLo otherZ, !(shiftGraph language) p p →
    !coverageGraph 0 f lo z p → !coverageGraph 0 g otherLo otherZ p →
    ∃ param target a b forward backward, !parametersGraph param 0 f lo z ∧
      !parametersGraph target 0 g otherLo otherZ ∧ !translateGraph a param p ∧
      !translateGraph b target p ∧ !biGraph forward backward a b”

theorem pa_proves_closed_parameter_relocation : theory ⊢ closedParameterSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [closedParameterSentence,models_iff,coverage_graph,parameters_graph,translate_graph,
    bi_graph,Matrix.comp_vecCons'']
  intro p f lo z g otherLo otherZ hc hl hr
  exact closed_formula_parameter_certificates p f lo z g otherLo otherZ hc.symm hl hr

#print axioms pa_proves_closed_parameter_relocation
#print axioms coverage_zero_environment
#print axioms coverage_reserve_raise
#print axioms closed_formula_parameter_certificates
end M6.PA.RelationalSource.Numeric

