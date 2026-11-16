import PA194ORData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194ORNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals (indexedNext indexedRun)

def runFrom (initial : PackedConf) (n : Nat) : PackedConf :=
  Nat.rec initial (fun _ c => indexedNext PA194ORData.rows c) n

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194ORData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b := by
  induction b with
  | zero => simp [runFrom]
  | succ b ih =>
    change indexedNext PA194ORData.rows (runFrom initial (a + b)) =
      indexedNext PA194ORData.rows (runFrom (runFrom initial a) b)
    rw [ih]

end PA194ORNumerical
