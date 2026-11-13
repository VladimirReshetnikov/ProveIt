module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentConnectiveNormalization
public import M6PA.Calibration.FoundationRelationalSequentPaddedProofEnvironment
public import M6PA.Calibration.FoundationRelationalSequentPaddingReadback
@[expose] public section

/-! Compose supplied source implications at a common raised proof budget,
then return the final source implication to exactly the requested labels. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric ActualCheckerBlueprint
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem source_implication_compose (a b c g lo z : V)
    (ha:IsFormula L a) (hb:IsFormula L b) (hc:IsFormula L c)
    (hgoal:FormulaCovered 0 g lo z (imp L a c))
    (hab:∀g lo z, FormulaCovered 0 g lo z (imp L a b) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a b)+1)
    (hbc:∀g lo z, FormulaCovered 0 g lo z (imp L b c) →
      ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L b c)+1) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a c)+1 := by
  let d := max (imp L a b) (max (imp L b c) (imp L a c))
  have he := padded_proofEnvironment d g lo z hgoal.1.1
  have cab : FormulaCovered 0 (padEnvironment g d) lo (z+lo+d) (imp L a b) :=
    he.coverage (IsSemiformula.imp.mpr ⟨ha,hb⟩) (le_max_left _ _)
  have cbc : FormulaCovered 0 (padEnvironment g d) lo (z+lo+d) (imp L b c) :=
    he.coverage (IsSemiformula.imp.mpr ⟨hb,hc⟩) ((le_max_left _ _).trans (le_max_right _ _))
  let param := parameters 0 (padEnvironment g d) lo (z+lo+d)
  obtain ⟨x,hx⟩ := hab _ _ _ cab
  obtain ⟨y,hy⟩ := hbc _ _ _ cbc
  obtain ⟨xf,_,hxf,_⟩ := translate_imp_certificates param a b ha.isUFormula hb.isUFormula
  obtain ⟨yf,_,hyf,_⟩ := translate_imp_certificates param b c hb.isUFormula hc.isUFormula
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param a c ha.isUFormula hc.isUFormula
  let left := (⟨x,hx⟩ : Certificate (translate param (imp L a b))).mp ⟨xf,hxf⟩
  let right := (⟨y,hy⟩ : Certificate (translate param (imp L b c))).mp ⟨yf,hyf⟩
  let composed := implicationCompose left right
  let result := composed.mp ⟨back,hback⟩
  exact padded_proof_certificate_readback (imp L a c) g lo z d result.code hgoal result.accepted

#print axioms source_implication_compose
end M6.PA.NumericPAeqValueTotality

