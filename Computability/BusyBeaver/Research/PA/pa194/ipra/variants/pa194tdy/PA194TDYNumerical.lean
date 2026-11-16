import PA194TDYData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194TDYNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA194TDYData.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194TDYData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA194TDYData.rows initial a b

end PA194TDYNumerical
