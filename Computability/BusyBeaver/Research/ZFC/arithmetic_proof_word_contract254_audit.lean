import BusyBeaver.ZFC.ArithmeticProofWordContract254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandRun254 ArithmeticProofWord254
open ArithmeticProofWordContract254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.good_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.prefixGood_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.good_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.contract_of_good
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.major_input_of_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordContract254.good_of_step
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : 𝚷₁-Predicate (Good (V := V)) := good_definable
example : 𝚷₁-Predicate (PrefixGood (V := V)) := prefixGood_definable
example : Good (0 : V) := good_zero
example (code : V) (hg : Good code) (hv : ArithmeticHistory254.value code ≠ 0) :
    Contract (rawWord code) (ArithmeticHistory254.value code - 1) := contract_of_good hg hv
example (bound child minorTarget stack : V) (hp : PrefixGood bound) (hi : child ≤ bound)
    (hv : ArithmeticHistory254.value child ≠ 0) :
    evalValue (rawWord child) (stateValue 0 (cantor minorTarget stack) 0 0) = 0 ∨
      evalValue (rawWord child) (stateValue 0 (cantor minorTarget stack) 0 0) =
        someState (ArithmeticHistory254.value child - 1) (cantor minorTarget stack) 0 0 :=
  major_input_of_prefix hp hi hv minorTarget stack
example (step : ∀ raw : V, PrefixGood raw → Good (raw + 1)) : ∀ code : V, Good code :=
  good_of_step step
example (step : ∀ raw : V, PrefixGood raw → Good (raw + 1)) (code : V)
    (hv : ArithmeticHistory254.value code ≠ 0) :
    Contract (rawWord code) (ArithmeticHistory254.value code - 1) :=
  contract_of_good (good_of_step step code) hv
example (code : V) (hv : ArithmeticHistory254.value code = 0) : Good code := Or.inl hv
