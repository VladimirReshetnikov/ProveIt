import BusyBeaver.ZFC.ArithmeticHistory222
import BusyBeaver.ZFC.ArithmeticHistory254

set_option autoImplicit false
set_option Elab.async false

/-! All-code Nat interpretation of the actual represented C222 evaluator.
The old history module supplies only generic Nat division/remainder and
numeral identities. No old history/checker semantic theorem is used, and no
second numeric history or fuel evaluator is defined. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistory222Nat

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticHistory222

/-- Bind the represented positive selector to the actual numeric C222 row
with the same total sequence-lookup oracle. -/
theorem positiveStep_nat (s raw : Nat) :
    positiveStep s raw = ArithmeticRow222.row (znth s) (raw % 12) (raw / 12) := by
  unfold positiveStep
  rw [← ArithmeticHistory254.numeral_twelve_eq_twelve, ← numeral_two_eq_two]
  simp only [Nat.numeral_eq, HMod.hMod, HDiv.hDiv]
  rw [ArithmeticHistory254.foundation_rem_nat, ArithmeticHistory254.foundation_div_nat]
  by_cases h : raw % 12 = 2 <;>
    simpa [second_nat, first_nat, HMod.hMod, HDiv.hDiv, h] using
      ArithmeticRow222.rowKernel_nat (znth s) (raw % 12) (raw / 12)

/-- Every queried child already occurs in this same represented history. -/
theorem value_succ_nat (raw : Nat) :
    value (raw + 1) = ArithmeticRow222.row value (raw % 12) (raw / 12) := by
  rw [value_succ_step, positiveStep_nat]
  apply ArithmeticRow222.row_congr
  intro i hi
  apply history_lookup_le raw i
  rw [Arithmetic.le_def]
  have hp : raw / 12 ≤ raw := Nat.div_le_self raw 12
  omega

/-- All-code agreement at every fuel strictly greater than the code. Strong
induction supplies smaller child codes at the smaller fuel; no parser fuel
monotonicity or valid-tree premise is needed. -/
theorem value_nat_fuel (code : Nat) : ∀ fuel, code < fuel →
    value code = ArithmeticRow222.parsedValue (Code254Proof.decodeFuel fuel code) := by
  induction code using Nat.strong_induction_on with
  | h code ih =>
      intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
          cases code with
          | zero => simp [Code254Proof.decodeFuel, ArithmeticRow222.parsedValue]
          | succ raw =>
              rw [value_succ_nat]
              simp only [Code254Proof.decodeFuel]
              rw [← ArithmeticRow222.row_parsedValue]
              apply ArithmeticRow222.row_congr
              intro i hi
              have hp : raw / 12 ≤ raw := Nat.div_le_self raw 12
              exact ih i (by omega) fuel (by omega)

/-- The concrete checker uses precisely this fuel, even on malformed codes. -/
theorem value_nat (code : Nat) :
    value code = ArithmeticRow222.parsedValue (Code254Proof.decodeFuel (code + 1) code) :=
  value_nat_fuel code (code + 1) (Nat.lt_succ_self code)

theorem valueDef_nat (output code : Nat) :
    valueDef.val.Evalb ![output, code] ↔
      output = ArithmeticRow222.parsedValue (Code254Proof.decodeFuel (code + 1) code) := by
  have h := (value_defined (V := Nat)).df ![output, code]
  change valueDef.val.Evalb ![output, code] ↔ output = value code at h
  rw [value_nat] at h
  exact h

/-- Exact interpretation of the fixed acceptance formula on EVERY pair of
natural inputs, not only constructor quotations. -/
theorem checkDef_nat (code conclusion : Nat) :
    checkDef.val.Evalb ![code, conclusion] ↔ Code222Proof.check222 code conclusion = true := by
  have h := (check_defined (V := Nat)).df ![code, conclusion]
  change checkDef.val.Evalb ![code, conclusion] ↔ value code = conclusion + 1 at h
  rw [value_nat] at h
  refine h.trans ?_
  unfold Code222Proof.check222
  cases hp : Code254Proof.decodeFuel (code + 1) code with
  | none => simp [ArithmeticRow222.parsedValue]
  | some p =>
      cases hv : Code222Proof.valid222 p <;>
        simp [ArithmeticRow222.parsedValue, hv]

theorem checkValue_nat (code conclusion : Nat) :
    checkValue code conclusion =
      if Code222Proof.check222 code conclusion = true then 1 else 0 := by
  classical
  have h : value code = conclusion + 1 ↔ Code222Proof.check222 code conclusion = true := by
    have hd := (check_defined (V := Nat)).df ![code, conclusion]
    change checkDef.val.Evalb ![code, conclusion] ↔ value code = conclusion + 1 at hd
    exact hd.symm.trans (checkDef_nat code conclusion)
  simp only [checkValue, h]

/-- External actual C222 derivability agrees with existence of a natural
witness to this same fixed represented formula. This is not an internal
seed-validity, interpreter-runtime or HA-equivalence theorem. -/
theorem c222_iff_represented (conclusion : Nat) :
    KCode222.C222 conclusion ↔ ∃ code, checkDef.val.Evalb ![code, conclusion] := by
  rw [Code222Proof.c222_iff_checked]
  exact exists_congr fun code => (checkDef_nat code conclusion).symm

end SetTheory.BusyBeaver.ZFC.ArithmeticHistory222Nat
