import PA194LCAX11HData
import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194LCAX11HNumerical
open ConPA.Machine (PackedConf)
open PA194IndexedNumerals

abbrev runFrom : PackedConf → Nat → PackedConf := indexedRunFrom PA194LCAX11HData.rows

theorem blank (n : Nat) : runFrom (0,0,0) n = indexedRun PA194LCAX11HData.rows n := rfl

theorem run_add (initial : PackedConf) (a b : Nat) :
    runFrom initial (a + b) = runFrom (runFrom initial a) b :=
  indexedRunFrom_add PA194LCAX11HData.rows initial a b

end PA194LCAX11HNumerical
