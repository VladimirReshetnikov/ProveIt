module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentPrefixAgreement
public import M6PA.Calibration.FoundationRelationalSequentClosedRelocation
@[expose] public section

/-! Returning an accepted proof from a padded environment and larger reserve
keeps the requested allocator and every original free label. No closedness
hypothesis is needed. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem padded_formula_certificate_readback (p b f lo z n other code : V)
    (hc : FormulaCovered b f lo z p) (hz : z≤other)
    (hcode : verifyValue code=translate (parameters b (padEnvironment f n) lo other) p+1) :
    ∃ out, verifyValue out=translate (parameters b f lo z) p+1 := by
  rw [translate_padEnvironment p b f lo other n hc.2.1.isUFormula hc.2.2] at hcode
  obtain ⟨forward,backward,hforward,hbackward⟩ := formula_reserve_certificates
    p b f lo z other hc (coverage_reserve_raise hc hz)
  let out := (⟨code,hcode⟩ : Certificate (translate (parameters b f lo other) p)).mp
    ⟨backward,hbackward⟩
  exact ⟨out.code,out.accepted⟩

theorem padded_proof_certificate_readback (p f lo z d code : V)
    (hc : FormulaCovered 0 f lo z p)
    (hcode : verifyValue code=
      translate (parameters 0 (padEnvironment f d) lo (z+lo+d)) p+1) :
    ∃ out, verifyValue out=translate (parameters 0 f lo z) p+1 :=
  padded_formula_certificate_readback p 0 f lo z d (z+lo+d) code hc (by simp) hcode

attribute [local irreducible] prefixAgreementGraph freePrefixGraph coverageGraph
  parametersGraph translateGraph padEnvironmentGraph verifyGraph
noncomputable def prefixAgreementSentence : ArithmeticSentence :=
  “∀ p b f g lo z, !((isUFormula language).sigma) p →
    !freePrefixGraph p f g → !prefixAgreementGraph p b f g lo z”

theorem pa_proves_prefixAgreement : theory ⊢ prefixAgreementSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [prefixAgreementSentence,models_iff,freePrefix_graph,prefixAgreement_graph,Matrix.comp_vecCons'']
  intro p b f g lo z hp h
  exact translate_free_prefix p b f g lo z hp h

noncomputable def paddingReadbackSentence : ArithmeticSentence :=
  “∀ p b f lo z n other code, !coverageGraph b f lo z p → z≤other →
    (∃ padded param a, !padEnvironmentGraph padded f n ∧
      !parametersGraph param b padded lo other ∧ !translateGraph a param p ∧ !verifyGraph (a+1) code) →
    ∃ param a out, !parametersGraph param b f lo z ∧ !translateGraph a param p ∧ !verifyGraph (a+1) out”

theorem pa_proves_padding_readback : theory ⊢ paddingReadbackSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [paddingReadbackSentence,models_iff,coverage_graph,padEnvironment_graph,
    parameters_graph,translate_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]
  intro p b f lo z n other code hc hz hcode
  exact padded_formula_certificate_readback p b f lo z n other code hc hz hcode

#print axioms padded_formula_certificate_readback
#print axioms padded_proof_certificate_readback
#print axioms pa_proves_prefixAgreement
#print axioms pa_proves_padding_readback
end M6.PA.RelationalSource.Numeric

