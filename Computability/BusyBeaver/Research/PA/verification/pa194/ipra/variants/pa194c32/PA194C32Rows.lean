import PA194C32Data
import PA194TableRows
import PA194IndexedNumerals

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194C32Rows
open PA194C32Data ConPA.Machine

theorem listedValid : ∀ i : Fin labels.length, ∀ b : Bool,
    PA194TableRows.validNative labels rows nativeTree (labels.getD i.val 254) b = true := by
  decide +kernel

theorem keysListed : nativeTree.keys.all (fun q => decide (q ∈ labels)) = true := by
  decide +kernel

theorem rowAgreement : Compressed.RowAgreement table machine denseControl :=
  PA194TableRows.rowAgreement labels rows nativeTree keysListed
    listedValid

theorem rootControl : denseControl 84 = 24 := by decide +kernel
theorem haltControl : denseControl 254 = 194 := by decide +kernel
theorem directions : PA194IndexedNumerals.BinaryDirections rows := by
  unfold PA194IndexedNumerals.BinaryDirections
  decide +kernel

#print axioms rowAgreement
#print axioms directions
end PA194C32Rows
