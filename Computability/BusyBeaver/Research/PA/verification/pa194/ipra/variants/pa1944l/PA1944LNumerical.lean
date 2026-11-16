import PA1944LData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA1944LNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA1944LData.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA1944LData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA1944LData.rows initial a b

end PA1944LNumerical
