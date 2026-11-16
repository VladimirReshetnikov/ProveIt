import PA194M6Numerical
import PA1944LRestrictedComplete

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194M6Startup
open PA194M6Numerical PA194IndexedRunRestriction

theorem agreesOutside :
    ∀ (q : Fin 194) (b : Fin 2), ([107, 123] : List Nat).contains q.val = false →
      PA1944LData.rows.getD (2 * q.val + b.val) (0, 0, 194) =
        PA194M6Data.rows.getD (2 * q.val + b.val) (0, 0, 194) := by
  decide +kernel

theorem startup : runFrom (0,0,0) 58320 =
      (24, 1, 152919395647067130113387679226998336721518593) := by
  have equal := transfer PA1944LData.rows PA194M6Data.rows [107, 123]
    (fun q b hq hb safe => agreesOutside ⟨q,hq⟩ ⟨b,hb⟩ safe) (0,0,0) 58320
    (congrArg Prod.fst PA1944LRestricted.certificate)
  rw [PA1944LRestricted.certificate] at equal
  exact equal

theorem seedPath : PA194M6Data.path 25 = PA194SourceProgram.path 25 := by decide +kernel
theorem seedGap : 48 - (PA194M6Data.path 25).length = 42 := by decide +kernel

#print axioms agreesOutside
#print axioms startup
#print axioms seedPath
#print axioms seedGap
end PA194M6Startup
