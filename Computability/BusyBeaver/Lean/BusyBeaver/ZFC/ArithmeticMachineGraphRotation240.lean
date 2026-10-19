import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252
import BusyBeaver.ZFC.TableRotation240

/-!
A fixed bounded arithmetic lookup for the exact source-rotation240 table.
The existing generic lookup compiler and numeric action convention are reused.
The literal table is imported, including its terminal write and movement;
zero action code still means an absent lookup, not a terminal transition.
Internal step iteration, startup and consistency calibration are separate.
The original machine and compiler retain Mira-Cult, Jeff Ketchersid and
Andrew James Wade's attribution; this instantiation follows the checked
prefix246 arithmetic interface and the exact source80 rotation table.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def rawActionNumber (a : RawActionRotation240) : Nat :=
  1 + 4 * (if a.2.2 < 240 then a.2.2 + 1 else 0) +
    2 * (if a.2.1 = .right then 1 else 0) + a.1.toNat

/-- Derived from the canonical table, without a second list of transitions. -/
def literalRows : List (Nat × Nat) :=
  rawTableRotation240.toList.map fun row => (rawActionNumber row.1, rawActionNumber row.2)

noncomputable def actionLookup (q bit : V) : V := lookupValue literalRows 0 q bit

def actionLookupDef : 𝚺₀.Semisentence 3 := lookupDef literalRows 0

instance actionLookup_defined : 𝚺₀-Function₂[V] actionLookup via actionLookupDef :=
  lookup_defined literalRows 0

theorem actionLookup_graph (out q bit : V) :
    actionLookupDef.val.Evalb ![out, q, bit] ↔ out = actionLookup q bit := by simp

theorem literalRows_length : literalRows.length = 240 := by decide +kernel

/-- The existing generic step formula uses this uniform constant bound. -/
theorem literalRows_positive_bounded :
    ∀ row ∈ literalRows, 0 < row.1 ∧ row.1 ≤ 1012 ∧ 0 < row.2 ∧ row.2 ≤ 1012 := by
  decide +kernel

theorem actionLookup_bound (q bit : V) :
    actionLookup q bit ≤ ORingStructure.numeral 1012 :=
  lookupValue_bound literalRows 0 q bit 1012 (by
    intro row hr
    have h := literalRows_positive_bounded row hr
    exact ⟨h.2.1, h.2.2.2⟩)

/-- All 480 actions agree with the exact typed machine, including halting. -/
theorem literal_lookup_actual :
    ∀ (q : Fin 240) (bit : Bool),
      lookupNat literalRows 0 (q.val + 1) bit.toNat =
        actionNumber (machineRotation240.transition q bit) := by decide +kernel

@[simp] theorem actionLookup_nat (q bit : Nat) :
    actionLookup q bit = lookupNat literalRows 0 q bit := lookup_nat _ _ _ _

theorem halt_action_number : actionNumber
    (machineRotation240.transition (oldStateRotation240 77) true) = 4 := by
  rw [machineRotation240_halt_action]
  rfl

theorem first_action_number : actionNumber
    (machineRotation240.transition (0 : Fin 240) false) = 392 := by decide +kernel

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineGraphRotation240
