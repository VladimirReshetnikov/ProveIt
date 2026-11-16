import PA194RegisterLayout
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace PA194C32Allocation
open PA194RegisterLayout

private def order : Fin 11 → Fin 11 := ![2,8,4,3,1,7,0,6,5,9,10]

def allocation : Allocation where
  order := order
  position := ![6,4,0,3,2,8,7,5,1]
  position_index := by intro r; fin_cases r <;> rfl
  order_inj := by
    have h : ∀ i j : Fin 11, order i = order j → i = j := by decide +kernel
    exact h
  first_spare := rfl
  suffix := rfl

#print axioms allocation
end PA194C32Allocation
