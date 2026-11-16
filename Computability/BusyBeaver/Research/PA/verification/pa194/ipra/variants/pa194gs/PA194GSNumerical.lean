import PA194GSData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194GSNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA194GSData.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194GSData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA194GSData.rows initial a b

end PA194GSNumerical
