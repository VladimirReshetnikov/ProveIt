import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194Site31UpdateVector
variable {M : Type} [Add M] [OfNat M 1]
theorem updateVector (v : Fin 11 → M) (suffix : M) :
    Function.update (Function.update v 6 (v 6+1)) 10 suffix =
      ![v 0,v 1,v 2,v 3,v 4,v 5,v 6+1,v 7,v 8,v 9,suffix] := by
  funext i
  fin_cases i <;> simp only [Function.update_apply, Fin.reduceEq, ite_true, ite_false] <;> rfl
#print axioms updateVector
end PA194Site31UpdateVector
