module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificateComposition
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric PA196.Arithmetic.Checker
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem source_certificate_mp (a b g lo z:V) (ha:IsFormula L a) (hb:IsFormula L b)
    (hgoal:FormulaCovered 0 g lo z b)
    (hA:∀g lo z,FormulaCovered 0 g lo z a→∃code,verifyValue code=translate (parameters 0 g lo z) a+1)
    (hAB:∀g lo z,FormulaCovered 0 g lo z (imp L a b)→
      ∃code,verifyValue code=translate (parameters 0 g lo z) (imp L a b)+1):
    ∃code,verifyValue code=translate (parameters 0 g lo z) b+1 := by
  let d := max a (max (imp L a b) b)
  have he := padded_proofEnvironment d g lo z hgoal.1.1
  have ca := he.coverage ha (le_max_left a (max (imp L a b) b))
  have cab := he.coverage (IsSemiformula.imp.mpr ⟨ha,hb⟩)
    ((le_max_left (imp L a b) b).trans (le_max_right a (max (imp L a b) b)))
  let param := parameters 0 (padEnvironment g d) lo (z+lo+d)
  obtain ⟨ac,hac⟩ := hA _ _ _ ca
  obtain ⟨abc,habc⟩ := hAB _ _ _ cab
  obtain ⟨forward,_,hforward,_⟩ := translate_imp_certificates param a b ha.isUFormula hb.isUFormula
  let arrow := (⟨abc,habc⟩ : Certificate (translate param (imp L a b))).mp ⟨forward,hforward⟩
  let out := (⟨ac,hac⟩ : Certificate (translate param a)).mp arrow
  exact padded_proof_certificate_readback b g lo z d out.code hgoal out.accepted
#print axioms source_certificate_mp
end PA196.Arithmetic.Transport.NumericPAeqValueTotality

