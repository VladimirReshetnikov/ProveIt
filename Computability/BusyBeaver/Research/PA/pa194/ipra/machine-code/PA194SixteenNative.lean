import PRAEqualityToIPRA
import PA194SixteenScanInvariant

/-! This is a local physical scanner identity, not a consistency reduction. -/
set_option autoImplicit false
namespace PA194SixteenNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAStandardTheory

theorem scan : standardTheory ⊢ equalClosureI PA194SixteenScanInvariant.fullLeft PA194SixteenScanInvariant.fullRight := by
  apply PRAEqualityToIPRA.nativeOfClassical
  exact PA194SixteenScanInvariant.PRA_proves_fullScanSentence
#print axioms scan
end PA194SixteenNative
