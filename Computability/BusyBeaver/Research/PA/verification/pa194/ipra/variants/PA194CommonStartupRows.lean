import PA1944LData
import PA194LCAData
import PA194M4RData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194CommonStartupRows

theorem lca : ∀ (q : Fin 194) (b : Fin 2), ([107, 123] : List Nat).contains q.val = false →
    PA1944LData.rows.getD (2 * q.val + b.val) (0, 0, 194) =
      PA194LCAData.rows.getD (2 * q.val + b.val) (0, 0, 194) := by decide +kernel

theorem m4r : ∀ (q : Fin 194) (b : Fin 2), ([107, 123] : List Nat).contains q.val = false →
    PA1944LData.rows.getD (2 * q.val + b.val) (0, 0, 194) =
      PA194M4RData.rows.getD (2 * q.val + b.val) (0, 0, 194) := by decide +kernel

#print axioms lca
#print axioms m4r
end PA194CommonStartupRows
