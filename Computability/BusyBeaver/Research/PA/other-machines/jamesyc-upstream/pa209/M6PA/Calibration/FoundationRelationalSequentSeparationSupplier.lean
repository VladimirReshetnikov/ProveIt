module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentSeparationReadback
@[expose] public section

/-! Uniform accepted source Separation schema over arbitrary PA-model formula
codes. The exact source constructor and endpoint coverage are explicit. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem source_separation_certificate (p f lo z : V)
    (hp : IsSemiformula language 1 p) (hc : FormulaCovered 0 f lo z (sourceSeparation p)) :
    ∃ code, verifyValue code=translate (parameters 0 f lo z) (sourceSeparation p)+1 := by
  have hprop := separation_property_coverage hc hp
  have hfresh := separation_output_fresh hc hp
  obtain ⟨ha,hd,hca,hcd⟩ := separation_label_bounds hc hp
  obtain ⟨raw,hraw⟩ := covered_separation_at_name p lo (lo+1+1) (lo+1)
    ((lo+1+1)∷0) f (lo+1+1+1) z hprop hfresh ha hd hca hcd
  obtain ⟨forward,backward,hforward,hbackward⟩ := separation_readback_certificates p f lo z hp
  let allRaw := (⟨raw,hraw⟩ : Certificate (separationValue lo (lo+1+1) (lo+1)
    (translate (parameters ((lo+1+1)∷0) f (lo+1+1+1) z) p))).all lo
  let out := allRaw.mp ⟨backward,hbackward⟩
  exact ⟨out.code,out.accepted⟩

attribute [local irreducible] sourceSeparationGraph coverageGraph parametersGraph translateGraph verifyGraph
noncomputable def sourceSeparationSentence : ArithmeticSentence :=
  “∀ p f lo z schema, !((isSemiformula language).sigma) 1 p →
    !sourceSeparationGraph schema p → !coverageGraph 0 f lo z schema →
    ∃ param out code, !parametersGraph param 0 f lo z ∧ !translateGraph out param schema ∧
      !verifyGraph (out+1) code”

theorem pa_proves_source_separation : theory ⊢ sourceSeparationSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [sourceSeparationSentence,models_iff,sourceSeparation_graph,coverage_graph,parameters_graph,
    translate_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]
  intro p f lo z hp hc
  exact source_separation_certificate p f lo z hp hc

#print axioms source_separation_certificate
#print axioms pa_proves_source_separation
end M6.PA.RelationalSource.Numeric

