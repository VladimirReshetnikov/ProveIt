import PA194LCData
import PA194TableRows

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194LCRows
open PA194LCData ConPA.Machine

def validNative : Nat → Bool → Bool := PA194TableRows.validNative labels rows nativeTree

theorem listed_valid : ∀ i : Fin 195, ∀ b : Bool, validNative (labels.getD i.val 254) b = true := by
  decide +kernel

theorem labels_length : labels.length = 195 := by decide +kernel

theorem keys_listed : nativeTree.keys.all (fun q => decide (q ∈ labels)) = true := by
  decide +kernel

theorem rowAgreement : Compressed.RowAgreement table machine denseControl :=
  PA194TableRows.rowAgreement labels rows nativeTree keys_listed
    (fun i b => listed_valid ⟨i.val, by rw [← labels_length]; exact i.isLt⟩ b)

#print axioms rowAgreement
end PA194LCRows
