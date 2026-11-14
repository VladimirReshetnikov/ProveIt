import PRAEqualityToIPRA
import PA194TwelveScanInvariant

/-! This is a local physical scanner identity, not a consistency reduction. -/
set_option autoImplicit false
namespace PA194TwelveNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAStandardTheory

theorem scan : standardTheory ⊢ equalClosureI PA194TwelveScanInvariant.fullLeft PA194TwelveScanInvariant.fullRight := by
  apply PRAEqualityToIPRA.nativeOfClassical
  exact PA194TwelveScanInvariant.PRA_proves_fullScanSentence
#print axioms scan
end PA194TwelveNative
