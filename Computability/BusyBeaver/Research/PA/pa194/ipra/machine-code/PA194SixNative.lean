import PRAEqualityToIPRA
import PA194SixScanInvariant

/-! This is a local physical scanner identity, not a consistency reduction. -/
set_option autoImplicit false
namespace PA194SixNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAStandardTheory

theorem scan : standardTheory ⊢ equalClosureI PA194SixScanInvariant.fullLeft PA194SixScanInvariant.fullRight := by
  apply PRAEqualityToIPRA.nativeOfClassical
  exact PA194SixScanInvariant.PRA_proves_fullScanSentence
#print axioms scan
end PA194SixNative
