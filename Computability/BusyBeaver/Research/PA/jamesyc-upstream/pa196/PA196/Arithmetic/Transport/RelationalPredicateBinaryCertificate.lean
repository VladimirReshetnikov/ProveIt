module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryClosure
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateBinary

namespace PA196.Arithmetic.Transport.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem addition_requested_certificate (P Q : SF (V:=V) 1) (g lo z : V)
    (hc : FormulaCovered 0 g lo z (statement domain addition P Q).val) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (statement domain addition P Q).val+1 := by
  apply singleton_requested_certificate (totalityReverse domain addition) (statement domain addition P Q)
    (compositionReverse domain addition P Q) g lo z hc
  intro g lo z h
  rw [addition_closure] at h ⊢
  exact RelationalClosedCertificate.addition_certificate g lo z h

theorem multiplication_requested_certificate (P Q : SF (V:=V) 1) (g lo z : V)
    (hc : FormulaCovered 0 g lo z (statement domain multiplication P Q).val) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (statement domain multiplication P Q).val+1 := by
  apply singleton_requested_certificate (totality domain multiplication) (statement domain multiplication P Q)
    (composition domain multiplication P Q) g lo z hc
  intro g lo z h
  rw [multiplication_closure] at h ⊢
  exact RelationalClosedCertificate.multiplication_certificate g lo z h

#print axioms addition_requested_certificate
#print axioms multiplication_requested_certificate
end PA196.Arithmetic.Transport.RelationalPredicateBinary
