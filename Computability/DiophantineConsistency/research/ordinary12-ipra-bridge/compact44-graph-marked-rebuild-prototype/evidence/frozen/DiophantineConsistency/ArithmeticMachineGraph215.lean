import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
import DiophantineConsistency.DecimalMachine215

/-! A bounded arithmetic lookup for the actual715-digit decimal machine.
Rows are derived from its typed transitions. Structural list lookup, rather
than repeated evaluation of the decoder, proves all430 action bindings.
Zero encodes an absent source lookup; halted successor actions stay positive
and retain their write and direction. No consistency calibration is claimed. -/
namespace DiophantineConsistency.ArithmeticMachineGraph215

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] DecimalMachine215.machine

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def literalRows : List (Nat × Nat) := List.ofFn fun q : Fin 215 =>
  (actionNumber (DecimalMachine215.machine.transition q false),
   actionNumber (DecimalMachine215.machine.transition q true))

/-- Generic indexed lookup includes every finite row and both actual bits. -/
theorem lookup_ofFn {n : ℕ} (f : Fin n → ℕ × ℕ) (q : Fin n) (bit : Bool)
    (first : ℕ) : lookupNat (List.ofFn f) first (first+q.val+1) bit.toNat =
      if bit then (f q).2 else (f q).1 := by
  induction n generalizing first with
  | zero => exact Fin.elim0 q
  | succ n ih =>
      rw [List.ofFn_succ]
      cases q using Fin.cases with
      | zero => cases bit <;> simp [lookupNat]
      | succ q =>
          have hn : first+q.succ.val+1 ≠ first+1 := by simp only [Fin.val_succ]; omega
          simp only [lookupNat, if_neg hn]
          have he : first+q.succ.val+1 = (first+1)+q.val+1 := by
            simp only [Fin.val_succ]; omega
          rw [he]
          exact ih (fun j => f j.succ) q (first+1)

theorem actionNumber_bounds (a : Action 215) :
    0 < actionNumber a ∧ actionNumber a ≤ 864 := by
  have hs : stateCode a.next ≤ 215 := by
    cases a.next with
    | none => simp [stateCode]
    | some q => simp only [stateCode]; omega
  unfold actionNumber
  cases a.move <;> cases a.write <;> simp only [Bool.toNat_false, Bool.toNat_true,
    reduceCtorEq, if_true, if_false] <;> omega

theorem literalRows_length : literalRows.length = 215 := List.length_ofFn

theorem literalRows_positive_bounded :
    ∀ row ∈ literalRows, 0 < row.1 ∧ row.1 ≤ 864 ∧ 0 < row.2 ∧ row.2 ≤ 864 := by
  intro row hr
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨(actionNumber_bounds _).1,(actionNumber_bounds _).2,actionNumber_bounds _⟩

/-- Equality with the actual decimal machine, including every halt action. -/
theorem literal_lookup_actual (q : Fin 215) (bit : Bool) :
    lookupNat literalRows 0 (q.val+1) bit.toNat =
      actionNumber (DecimalMachine215.machine.transition q bit) := by
  have h := lookup_ofFn (fun q : Fin 215 =>
    (actionNumber (DecimalMachine215.machine.transition q false),
     actionNumber (DecimalMachine215.machine.transition q true))) q bit 0
  cases bit <;> simpa only [literalRows, Nat.zero_add, Bool.false_eq_true, if_false, if_true] using h

noncomputable def actionLookup (q bit : V) : V := lookupValue literalRows 0 q bit

def actionLookupDef : 𝚺₀.Semisentence 3 := lookupDef literalRows 0

instance actionLookup_defined : 𝚺₀-Function₂[V] actionLookup via actionLookupDef :=
  lookup_defined literalRows 0

theorem actionLookup_graph (out q bit : V) :
    actionLookupDef.val.Evalb ![out,q,bit] ↔ out=actionLookup q bit := by simp

theorem actionLookup_bound (q bit : V) :
    actionLookup q bit ≤ ORingStructure.numeral 1012 :=
  lookupValue_bound literalRows 0 q bit 1012 (by
    intro row hr
    have h := literalRows_positive_bounded row hr
    exact ⟨by omega,by omega⟩)

@[simp] theorem actionLookup_nat (q bit : Nat) :
    actionLookup q bit = lookupNat literalRows 0 q bit := lookup_nat _ _ _ _

end DiophantineConsistency.ArithmeticMachineGraph215
