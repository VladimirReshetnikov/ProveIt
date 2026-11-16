module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCertificatePair
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric PA196.Arithmetic.Checker
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem source_identity_certificate (param a:V) (ha:IsUFormula L a):
    ∃code,verifyValue code=translate param (imp L a a)+1 := by
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param a a ha ha
  let assume : Context [translate param a] (translate param a) := .assumption (by simp)
  let out := assume.deduction.empty.mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩
theorem source_conjunction_projection (param a b:V) (ha:IsUFormula L a) (hb:IsUFormula L b) (left:Bool):
    ∃code,verifyValue code=translate param (imp L (qqAnd a b) (if left then a else b))+1 := by
  have ht : IsUFormula L (if left then a else b) := by cases left <;> simpa
  obtain ⟨_,back,_,hback⟩ := translate_imp_certificates param (qqAnd a b) _ (IsUFormula.and.mpr ⟨ha,hb⟩) ht
  let A := translate param a
  let B := translate param b
  let assume : Context [wa A B] (wa A B) := .assumption (by simp)
  have arrow : ∃code,verifyValue code=wim (translate param (qqAnd a b)) (translate param (if left then a else b))+1 := by
    rw [translate_and _ _ _ ha hb,translationAnd_eq]
    cases left
    · exact ⟨assume.andRight.deduction.empty.code,assume.andRight.deduction.empty.accepted⟩
    · exact ⟨assume.andLeft.deduction.empty.code,assume.andLeft.deduction.empty.accepted⟩
  obtain ⟨code,hcode⟩ := arrow
  let out := (⟨code,hcode⟩:Certificate _).mp ⟨back,hback⟩
  exact ⟨out.code,out.accepted⟩
#print axioms source_identity_certificate
#print axioms source_conjunction_projection
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
