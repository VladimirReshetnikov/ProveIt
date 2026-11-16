module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentRawSeparation
public import M6PA.Calibration.FoundationRelationalSequentVacuity
public import M6PA.Calibration.ActualCertificateSeparationRelocation
@[expose] public section

/-! Arbitrary covered source property separation at an explicitly fresh low
output label. This is native readback, not yet a source schema constructor. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem covered_separation_at_name (p a d c b f lo z : V)
    (hc : FormulaCovered b f lo z p) (hf : FreshEnvironment c b f lo z)
    (ha : a<z) (hd : d<z) (hca : c≠a) (hcd : c≠d) :
    ∃ code, verifyValue code=separationValue a d c (translate (parameters b f lo z) p)+1 := by
  let property := translate (parameters b f lo z) p
  let q := separationPadding a d z property
  have hq : z<q := separationPadding_above a d z property
  have hcz : c<z := lt_of_lt_of_le hf.1 hc.1.1.2.1
  obtain ⟨raw,hraw⟩ := covered_raw_separation p a d b f lo z hc ha.le hd.le
  obtain ⟨cv,hcv⟩ := covered_padding_vacuity p a d b f lo z hc
  obtain ⟨dv,hdv⟩ := formula_vacuity_certificate p c b f lo z hc hf
  let alpha := separationOutputAlpha a d q c z property (ne_of_lt hq)
    (Ne.symm (ne_of_lt hcz)) (Ne.symm (ne_of_lt hd))
    (Ne.symm (ne_of_lt (lt_trans ha hq))) (Ne.symm (ne_of_lt (lt_trans hd hq)))
    hca hcd (Ne.symm (ne_of_lt (lt_trans hcz hq))) ⟨cv,hcv⟩ ⟨dv,hdv⟩
  let out := (⟨raw,hraw⟩ : Certificate (separationValue a d q property)).mp alpha.forward
  exact ⟨out.code,out.accepted⟩

#print axioms covered_separation_at_name
end M6.PA.RelationalSource.Numeric

