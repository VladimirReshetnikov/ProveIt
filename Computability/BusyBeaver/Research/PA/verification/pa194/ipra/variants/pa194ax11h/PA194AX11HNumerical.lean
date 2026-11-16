import PA194AX11HData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194AX11HNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA194AX11HData.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194AX11HData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA194AX11HData.rows initial a b

end PA194AX11HNumerical
