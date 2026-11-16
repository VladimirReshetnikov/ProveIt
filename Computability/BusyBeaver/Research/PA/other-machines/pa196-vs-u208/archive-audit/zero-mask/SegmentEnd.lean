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
theorem segmentedCertificate26 : segmentedCertificate 26 = site26 := by decide
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

/-- At source ordinal 26, the archived invariant forces registers 3, 6, and 7
    to zero for every run from the certificate seed. -/
theorem source_26_zero
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 26, registers⟩) :
    registers 3 = 0 ∧ registers 6 = 0 ∧ registers 7 = 0 := by
  have hm : site26.testBit (encode (mask registers)) = true := by
    simpa only [segmentedCertificate26] using source_seed_mask_invariant 26 registers run
  let m : Fin 512 := ⟨encode (mask registers), encode_bound (mask registers)⟩
  have h3 := site26_reg3_zero m hm
  have h6 := site26_reg6_zero m hm
  have h7 := site26_reg7_zero m hm
  change (encode (mask registers)).testBit ((3 : Fin 9) : Nat) = false at h3
  change (encode (mask registers)).testBit ((6 : Fin 9) : Nat) = false at h6
  change (encode (mask registers)).testBit ((7 : Fin 9) : Nat) = false at h7
  have hm3 : mask registers 3 = false := by simpa only [encode_testBit] using h3
  have hm6 : mask registers 6 = false := by simpa only [encode_testBit] using h6
  have hm7 : mask registers 7 = false := by simpa only [encode_testBit] using h7
  exact ⟨by simpa [mask] using hm3, by simpa [mask] using hm6, by simpa [mask] using hm7⟩

theorem source_26_instruction : resolveAt PA196.Program.sites 26 = some (.jump (some 34)) := by
  rw [resolver_binding]
  decide

/-- At a reachable ordinal-26 frame, the proposed zero-decrement instruction
    has exactly the same source effect as the original jump. -/
theorem source_26_zero_decrement
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 26, registers⟩) :
    execute (.dec 6 (some 34) (some 27)) registers =
      step PA196.Program.sites ⟨.at 26, registers⟩ := by
  have hz := (source_26_zero registers run).2.1
  simp [step, source_26_instruction, execute, hz]

/-- Every source run from the certificate seed that reaches ordinal 3692
    has registers 3, 4, 5, and 6 equal to zero. -/
theorem source_3692_zero
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 3692, registers⟩) :
    registers 3 = 0 ∧ registers 4 = 0 ∧ registers 5 = 0 ∧ registers 6 = 0 :=
  source_zero_of_resolver_binding resolver_binding registers run
#print axioms segmentedCertificate25
#print axioms segmentedCertificate26
#print axioms segmentedCertificate3692
#print axioms source_zero_of_resolver_binding
#print axioms source_seed_mask_invariant
#print axioms source_26_zero
#print axioms source_26_instruction
#print axioms source_26_zero_decrement
#print axioms source_3692_zero
end PA196ZeroMask
