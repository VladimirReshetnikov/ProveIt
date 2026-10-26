import BusyBeaver.ZFC.ArithmeticRow222

set_option autoImplicit false
set_option Elab.async false

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticRow222

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example : 𝚺₀-Function₄[V] rowKernel via rowDef := row_defined
example (k p u v : V) (h9 : k ≠ 9) (h11 : k ≠ 11) :
    rowKernel k p u v = ArithmeticRow254.rowKernel k p u v :=
  rowKernel_unchanged k p u v h9 h11
end

example (rec : Nat → Nat) (a b c : Nat) :
    row rec 9 (Code254.P a (Code254.P b c)) = KCode222.growG a b c + 1 := by
  simp [row, Code254.unP_P]

-- Legal repeated labels and zero private binder keep the actual two gates.
example (rec : Nat → Nat) :
    row rec 11 (Code254.P 1 (Code254.P 1 0)) = KCode222.bundle222 1 1 0 + 1 := by
  simp [row, Code254.unP_P]
example (rec : Nat → Nat) (a b : Nat) : row rec 11 (Code254.P a (Code254.P b a)) = 0 := by
  simp [row, Code254.unP_P]
example (rec : Nat → Nat) (a b : Nat) : row rec 11 (Code254.P a (Code254.P b b)) = 0 := by
  simp [row, Code254.unP_P]

example (rec : Nat → Nat) (tag payload : Nat) (h : 12 ≤ tag) : row rec tag payload = 0 :=
  row_invalid rec tag payload h
example (rec : Nat → Nat) (tag payload output : Nat) :
    rowDef.val.Evalb (ArithmeticRow254.rowEnv rec tag payload output) ↔
      output = row rec tag payload := rowGraph_nat rec tag payload output
example (rec : Nat → Option Code254Proof.RawProof) (tag payload : Nat) :
    row (fun c => parsedValue (rec c)) tag payload =
      parsedValue (Code254Proof.decodeStep rec tag payload) := row_parsedValue rec tag payload

#print axioms rowKernel_unchanged
#print axioms rowKernel_growG
#print axioms rowKernel_bundle
#print axioms row_defined
#print axioms row_unchanged
#print axioms row_invalid
#print axioms rowKernel_nat
#print axioms rowGraph_nat
#print axioms row_parsedValue
#print axioms row_congr
