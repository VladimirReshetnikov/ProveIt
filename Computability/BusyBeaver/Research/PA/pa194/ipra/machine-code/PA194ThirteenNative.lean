import PRAEqualityToIPRA
import PA194ThirteenScanInvariant

/-! This is a local physical scanner identity, not a consistency reduction. -/
set_option autoImplicit false
namespace PA194ThirteenNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAStandardTheory

theorem scan : standardTheory ⊢ equalClosureI PA194ThirteenScanInvariant.fullLeft PA194ThirteenScanInvariant.fullRight := by
  apply PRAEqualityToIPRA.nativeOfClassical
  exact PA194ThirteenScanInvariant.PRA_proves_fullScanSentence
#print axioms scan
end PA194ThirteenNative
