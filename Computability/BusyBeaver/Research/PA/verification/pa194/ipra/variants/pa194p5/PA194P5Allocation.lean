import PA194RegisterLayout
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace PA194P5Allocation
open PA194RegisterLayout

private def order : Fin 11 → Fin 11 := ![2,8,3,1,4,7,0,6,5,9,10]

def allocation : Allocation where
  order := order
  position := ![6,3,0,2,4,8,7,5,1]
  position_index := by intro r; fin_cases r <;> rfl
  order_inj := by
    have h : ∀ i j : Fin 11, order i = order j → i = j := by decide +kernel
    exact h
  first_spare := rfl
  suffix := rfl

def physicalRegister (r : Fin 9) : Nat := (allocation.position r).val

#print axioms allocation
end PA194P5Allocation
