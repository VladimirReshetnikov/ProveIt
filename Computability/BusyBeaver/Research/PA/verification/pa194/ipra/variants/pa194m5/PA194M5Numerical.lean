import PA194M5Data
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194M5Numerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA194M5Data.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194M5Data.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA194M5Data.rows initial a b

end PA194M5Numerical
