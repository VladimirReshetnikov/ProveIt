module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryCode
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

theorem addition_supply (P Q g lo z : V) (hP : IsSemiformula L 1 P) (hQ : IsSemiformula L 1 Q)
    (hc : FormulaCovered 0 g lo z (binaryTotalityCode NumericPAeqTerm.additionTemplate P Q)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (binaryTotalityCode NumericPAeqTerm.additionTemplate P Q)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let q : SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  have h := statement_code NumericPAeqTerm.additionTemplate p q
  change (statement domain addition p q).val=_ at h
  exact h ▸ addition_requested_certificate p q g lo z (h.symm ▸ hc)

theorem multiplication_supply (P Q g lo z : V) (hP : IsSemiformula L 1 P) (hQ : IsSemiformula L 1 Q)
    (hc : FormulaCovered 0 g lo z (binaryTotalityCode NumericPAeqTerm.multiplicationTemplate P Q)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      (binaryTotalityCode NumericPAeqTerm.multiplicationTemplate P Q)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  let q : SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  have h := statement_code NumericPAeqTerm.multiplicationTemplate p q
  change (statement domain multiplication p q).val=_ at h
  exact h ▸ multiplication_requested_certificate p q g lo z (h.symm ▸ hc)
#print axioms addition_supply
#print axioms multiplication_supply
end PA196.Arithmetic.Transport.RelationalPredicateBinary

