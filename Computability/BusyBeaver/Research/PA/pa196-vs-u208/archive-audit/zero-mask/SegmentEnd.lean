import SegmentAll2
import Conclusion
/-! The archived source-frame conclusion, conditional only on table binding. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA196ZeroMask
open M6.Source

theorem segmentedCertificate25 : segmentedCertificate 25 = site25 := by decide
theorem segmentedCertificate3692 : segmentedCertificate 3692 = site3692 := by decide

theorem source_zero_of_resolver_binding
    (binding : ∀ pc, resolveAt PA196.Program.sites pc = segmentedLookup pc)
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 3692, registers⟩) :
    registers 3 = 0 ∧ registers 4 = 0 ∧ registers 5 = 0 ∧ registers 6 = 0 :=
  source_3692_zero_if_closed segmentedCertificate segmentedCertificate25 segmentedCertificate3692
    (closed_of_table PA196.Program.sites segmentedLookup segmentedCertificate binding archiveTableClosed)
    registers run
#print axioms segmentedCertificate25
#print axioms segmentedCertificate3692
#print axioms source_zero_of_resolver_binding
end PA196ZeroMask
