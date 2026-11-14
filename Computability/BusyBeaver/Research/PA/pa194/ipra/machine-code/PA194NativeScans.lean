import PRAEqualityToIPRA
import PA194ScanInvariant
import PA194ZeroScanInvariant

/-! Native-iPRA derivations of the two checked physical scan identities.
These do not prove a machine consistency equivalence. -/
set_option autoImplicit false
namespace PA194NativeScans
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAStandardTheory
open PRAEqualityToIPRA

theorem oneScan : standardTheory ⊢ equalClosureI PA194ScanInvariant.fullLeft PA194ScanInvariant.fullRight := by
  apply nativeOfClassical
  exact PA194ScanInvariant.PRA_proves_fullScanSentence

theorem zero : standardTheory ⊢ equalClosureI PA194ZeroScanInvariant.fullLeft PA194ZeroScanInvariant.fullRight := by
  apply nativeOfClassical
  exact PA194ZeroScanInvariant.PRA_proves_fullScanSentence
#print axioms oneScan
#print axioms zero
end PA194NativeScans
