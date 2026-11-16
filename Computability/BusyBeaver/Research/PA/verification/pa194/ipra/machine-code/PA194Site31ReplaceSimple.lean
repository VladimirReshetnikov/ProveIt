import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194Site31ReplaceSimple
variable {M : Type}
theorem replaceSix (v : Fin 11 → M) (marked t : M) :
    Fin.snoc (fun i : Fin 6 => (![v 0,v 1,v 2,v 3,v 4,v 5,marked] : Fin 7 → M) i.castSucc) t =
      ![v 0,v 1,v 2,v 3,v 4,v 5,t] := by
  funext i
  fin_cases i <;> rfl
#print axioms replaceSix

theorem replaceThree (v : Fin 11 → M) (suffix : M) :
    Fin.snoc (fun i : Fin 3 => v ⟨i.val+7,by omega⟩) suffix = ![v 7,v 8,v 9,suffix] := by
  funext i
  fin_cases i <;> rfl
#print axioms replaceThree
theorem vectorTail (v : Fin 11 → M) :
    (fun i : Fin 5 => (![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10] : Fin 11 → M) i.succ.succ.succ.succ.succ.succ) =
      ![v 6,v 7,v 8,v 9,v 10] := by
  funext i
  fin_cases i <;> rfl
#print axioms vectorTail
end PA194Site31ReplaceSimple
