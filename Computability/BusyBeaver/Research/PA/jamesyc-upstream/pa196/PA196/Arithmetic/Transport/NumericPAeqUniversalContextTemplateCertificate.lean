module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplateCode
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryEmptyRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
theorem context_requested_certificate (H S D P native lo z:V)
    (hH:IsFormula L H) (hS:IsFormula L S) (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P)
    (hc:FormulaCovered 0 native lo z (contextCode H S D P)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (contextCode H S D P)+1 := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let s:SF (V:=V) 0 := ⟨S,by simpa using hS⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have he := context_val h s d p
  change (uniform h s d p 🡒 (h 🡒 ((∀¹ (d 🡒 p)) ⋎ s))).val=contextCode H S D P at he
  rw [←he] at hc ⊢
  exact empty_requested_certificate _ (contextProof h s d p) native lo z hc
#print axioms context_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplate

