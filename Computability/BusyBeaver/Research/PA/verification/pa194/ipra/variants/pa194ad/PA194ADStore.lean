import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
namespace PA194ADStore

/-- Physical block occupied by each of the nine logical registers. -/
def primary : Fin 9 → Fin 9 := ![6,2,0,4,3,7,8,5,1]
def companion : Fin 9 → Fin 9 := ![6,2,0,3,4,7,8,5,1]

def swap (i : Fin 9) : Fin 9 := if i = 3 then 4 else if i = 4 then 3 else i

theorem swap_involutive (i : Fin 9) : swap (swap i) = i := by
  fin_cases i <;> decide

theorem map_swap (r : Fin 9) : swap (companion r) = primary r := by
  fin_cases r <;> decide

def transport {α : Type} (s : Fin 9 → α) : Fin 9 → α := fun i => s (swap i)

theorem logical_value {α : Type} (s : Fin 9 → α) (r : Fin 9) :
    transport s (companion r) = s (primary r) := by simp [transport, map_swap]

def change {α : Type} (s : Fin 9 → α) (i : Fin 9) (f : α → α) : Fin 9 → α :=
  fun j => if j = i then f (s i) else s j

/-- All unary updates, including successor and predecessor, commute with A/D allocation. -/
theorem update_transport {α : Type} (s : Fin 9 → α) (r : Fin 9) (f : α → α) :
    transport (change s (primary r) f) = change (transport s) (companion r) f := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [transport, change, primary, companion, swap]

/-- No numeric or standard-model assumption occurs in the zero-test identity. -/
theorem test_transport {α : Type} (s : Fin 9 → α) (r : Fin 9) (p : α → Prop) :
    p (transport s (companion r)) ↔ p (s (primary r)) := by rw [logical_value]

#print axioms swap_involutive
#print axioms map_swap
#print axioms logical_value
#print axioms update_transport
#print axioms test_transport
end PA194ADStore
