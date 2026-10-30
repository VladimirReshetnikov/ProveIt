import BusyBeaver.ZFC.ArithmeticMachinePerm252
import BusyBeaver.ZFC.ArithmeticHistory254

/-!
A finite bounded arithmetic lookup compiler instantiated with the actual frozen
252-state table. An action is encoded positively even when its next state is
halted; zero denotes an absent/invalid source-state lookup only. The numeric
whole-tape bridge is imported unchanged. Internal iteration is separate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- A finite lookup with literal numeral keys. Bit zero selects the first row;
every other input selects the second. Actual read bits are always zero or one. -/
noncomputable def lookupValue : List (Nat × Nat) → Nat → V → V → V
  | [], _, _, _ => 0
  | row :: rows, first, q, bit =>
    if q = ORingStructure.numeral (first + 1) then
      if bit = 0 then ORingStructure.numeral row.1 else ORingStructure.numeral row.2
    else lookupValue rows (first + 1) q bit

/-- Compilation into a fixed parameter-free bounded formula. The finite list
is syntax-construction data, not an arithmetic model parameter or an oracle. -/
def lookupDef : List (Nat × Nat) → Nat → 𝚺₀.Semisentence 3
  | [], _ => .mkSigma “r q bit. r = 0”
  | row :: rows, first => .mkSigma
    “r q bit.
      ((q = !!(Semiterm.Operator.numeral ℒₒᵣ (first + 1))) ∧
       ((bit = 0 ∧ r = !!(Semiterm.Operator.numeral ℒₒᵣ row.1)) ∨
        (bit ≠ 0 ∧ r = !!(Semiterm.Operator.numeral ℒₒᵣ row.2)))) ∨
      ((q ≠ !!(Semiterm.Operator.numeral ℒₒᵣ (first + 1))) ∧
        !(lookupDef rows (first + 1)) r q bit)”

instance lookup_defined (rows : List (Nat × Nat)) (first : Nat) :
    𝚺₀-Function₂[V] (lookupValue rows first) via lookupDef rows first := by
  induction rows generalizing first with
  | nil => exact .mk fun e => by simp [lookupDef, lookupValue]
  | cons row rows ih =>
    refine .mk fun e => ?_
    classical
    by_cases hq : e 1 = ORingStructure.numeral (first + 1)
    · by_cases hb : e 2 = 0 <;> simp [lookupDef, lookupValue, (ih (first + 1)).iff, hq, hb]
    · simp [lookupDef, lookupValue, (ih (first + 1)).iff, hq]

/-- Computable standard-model lookup, with exactly the same default policy. -/
def lookupNat : List (Nat × Nat) → Nat → Nat → Nat → Nat
  | [], _, _, _ => 0
  | row :: rows, first, q, bit =>
    if q = first + 1 then if bit = 0 then row.1 else row.2
    else lookupNat rows (first + 1) q bit

@[simp] theorem lookup_nat (rows : List (Nat × Nat)) (first q bit : Nat) :
    lookupValue rows first q bit = lookupNat rows first q bit := by
  induction rows generalizing first with
  | nil => rfl
  | cons row rows ih => simp [lookupValue, lookupNat, ih, Nat.numeral_eq]

lemma numeral_mono {a b : Nat} (h : a ≤ b) :
    (ORingStructure.numeral a : V) ≤ ORingStructure.numeral b := by
  simpa only [numeral_eq_natCast] using (Nat.cast_le (α := V)).mpr h

/-- A literal constant bound, independent of any rejected or halted result. -/
theorem lookupValue_bound (rows : List (Nat × Nat)) (first : Nat) (q bit : V)
    (bound : Nat) (hb : ∀ row ∈ rows, row.1 ≤ bound ∧ row.2 ≤ bound) :
    lookupValue rows first q bit ≤ ORingStructure.numeral bound := by
  induction rows generalizing first with
  | nil => exact Arithmetic.zero_le _
  | cons row rows ih =>
    classical
    have hr := hb row (by simp)
    by_cases hq : q = ORingStructure.numeral (first + 1)
    · by_cases hbit : bit = 0
      · simpa [lookupValue, hq, hbit] using (numeral_mono (V := V) hr.1)
      · simpa [lookupValue, hq, hbit] using (numeral_mono (V := V) hr.2)
    · simpa [lookupValue, hq] using ih (first + 1) (by
        intro r h; exact hb r (by simp [h]))

/-- Positive action code. Zero successor code is a real halt and does not erase
its write/move. Direction is zero for left and one for right. -/
def actionNumber {n : Nat} (a : Action n) : Nat :=
  1 + 4 * stateCode a.next + 2 * (if a.move = .right then 1 else 0) + a.write.toNat

def rawActionNumber (a : RawActionPerm252) : Nat :=
  1 + 4 * (if a.2.2 < 252 then a.2.2 + 1 else 0) +
    2 * (if a.2.1 = .right then 1 else 0) + a.1.toNat

/-- This is derived from the imported literal array, not a second table copy. -/
def literalRows : List (Nat × Nat) :=
  rawTablePerm252.toList.map fun row => (rawActionNumber row.1, rawActionNumber row.2)

noncomputable def actionLookup (q bit : V) : V := lookupValue literalRows 0 q bit

def actionLookupDef : 𝚺₀.Semisentence 3 := lookupDef literalRows 0

instance actionLookup_defined : 𝚺₀-Function₂[V] actionLookup via actionLookupDef :=
  lookup_defined literalRows 0

theorem literalRows_length : literalRows.length = 252 := by decide

theorem literalRows_positive_bounded :
    ∀ row ∈ literalRows, 0 < row.1 ∧ row.1 ≤ 1012 ∧ 0 < row.2 ∧ row.2 ≤ 1012 := by decide

theorem actionLookup_bound (q bit : V) :
    actionLookup q bit ≤ ORingStructure.numeral 1012 :=
  lookupValue_bound literalRows 0 q bit 1012 (by
    intro row hr
    have h := literalRows_positive_bounded row hr
    exact ⟨h.2.1, h.2.2.2⟩)

/-- Every one of the 504 typed transitions is the corresponding literal
lookup. The finite equality includes the unique halt successor and both bits. -/
theorem literal_lookup_actual :
    ∀ (q : Fin 252) (bit : Bool),
      lookupNat literalRows 0 (q.val + 1) bit.toNat =
        actionNumber (machinePerm252.transition q bit) := by decide

@[simp] theorem actionLookup_nat (q bit : Nat) :
    actionLookup q bit = lookupNat literalRows 0 q bit := lookup_nat _ _ _ _

/-- Explicit actual halt action: write one, move right, next state zero. -/
theorem halt_action_number : actionNumber
    (machinePerm252.transition (75 : Fin 252) true) = 4 := by decide

theorem first_action_number : actionNumber
    (machinePerm252.transition (0 : Fin 252) false) = 115 := by decide

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
