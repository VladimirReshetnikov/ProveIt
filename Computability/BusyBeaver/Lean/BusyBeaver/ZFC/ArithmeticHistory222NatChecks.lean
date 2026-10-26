import BusyBeaver.ZFC.ArithmeticHistory222Nat

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistory222NatChecks

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticHistory222 ArithmeticHistory222Nat

example (code fuel : Nat) (hf : code < fuel) :
    value code = ArithmeticRow222.parsedValue (Code254Proof.decodeFuel fuel code) :=
  value_nat_fuel code fuel hf

example (code conclusion : Nat) :
    checkDef.val.Evalb ![code, conclusion] ↔ Code222Proof.check222 code conclusion = true :=
  checkDef_nat code conclusion

example (conclusion : Nat) : ¬checkDef.val.Evalb ![0, conclusion] := by
  rw [checkDef_nat, Code222Proof.reject_zero]
  decide

example : checkDef.val.Evalb ![1, 0] :=
  (checkDef_nat 1 0).mpr Code222Proof.accept_truth

example (a b c : Nat) : checkDef.val.Evalb
    ![(Code254Proof.RawProof.r7 a b c).quote, KCode222.growG a b c] :=
  (checkDef_nat _ _).mpr (Code222Proof.accept_growG a b c)

example (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) : checkDef.val.Evalb
    ![(Code254Proof.RawProof.bundle a b c).quote, KCode222.bundle222 a b c] :=
  (checkDef_nat _ _).mpr (Code222Proof.accept_bundle a b c hca hcb)

/-- The legal zero binder and repeated equality labels are not excluded. -/
example : checkDef.val.Evalb
    ![(Code254Proof.RawProof.bundle 1 1 0).quote, KCode222.bundle222 1 1 0] :=
  (checkDef_nat _ _).mpr (Code222Proof.accept_bundle 1 1 0 (by decide) (by decide))

example (n : Nat) : KCode222.C222 n ↔ ∃code, checkDef.val.Evalb ![code, n] :=
  c222_iff_represented n

#print axioms positiveStep_nat
#print axioms value_succ_nat
#print axioms value_nat_fuel
#print axioms value_nat
#print axioms valueDef_nat
#print axioms checkDef_nat
#print axioms checkValue_nat
#print axioms c222_iff_represented

end SetTheory.BusyBeaver.ZFC.ArithmeticHistory222NatChecks
