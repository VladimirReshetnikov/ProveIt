import SegmentAll2
import Conclusion
import ResolverBinding
/-! The archived source-frame conclusion and its table binding. -/
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

/-- The archived mask set contains every source frame reached from the seed. -/
theorem source_seed_mask_invariant
    (pc : Nat) (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at pc, registers⟩) :
    (segmentedCertificate pc).testBit (encode (mask registers)) = true := by
  have seed : Holds (fun p m => (segmentedCertificate p).testBit (encode m) = true)
      ⟨.at 25, seedRegisters⟩ := by
    simp [Holds, segmentedCertificate25, seed_mask, seed_present]
  have reached := steps_preserve PA196.Program.sites
    (fun p m => (segmentedCertificate p).testBit (encode m) = true)
    (closed_of_table PA196.Program.sites segmentedLookup segmentedCertificate resolver_binding archiveTableClosed)
    run seed
  simpa [Holds] using reached

/-- Every source run from the certificate seed that reaches ordinal 3692
    has registers 3, 4, 5, and 6 equal to zero. -/
theorem source_3692_zero
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 3692, registers⟩) :
    registers 3 = 0 ∧ registers 4 = 0 ∧ registers 5 = 0 ∧ registers 6 = 0 :=
  source_zero_of_resolver_binding resolver_binding registers run
#print axioms segmentedCertificate25
#print axioms segmentedCertificate3692
#print axioms source_zero_of_resolver_binding
#print axioms source_seed_mask_invariant
#print axioms source_3692_zero
end PA196ZeroMask
