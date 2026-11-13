import Abstraction
import Zero
import PA196.Program

/-! Conditional application to the actual source program and archive masks.
The `Closed` hypothesis has not been established for the archive certificate. -/
set_option autoImplicit false
namespace PA196ZeroMask
open M6.Source

def seedRegisters : Registers := fun r => if r = 0 then 2 else 0

theorem seed_mask : encode (mask seedRegisters) = 1 := by decide

/-- If the numeric certificate is closed for the actual source resolver, all
    four registers are zero whenever its candidate-2 run reaches ordinal 3692. -/
theorem source_3692_zero_if_closed
    (certificate : Nat → Nat)
    (h25 : certificate 25 = site25)
    (h3692 : certificate 3692 = site3692)
    (closed : Closed PA196.Program.sites
      (fun pc m => (certificate pc).testBit (encode m) = true))
    (registers : Registers) {n : Nat}
    (run : Steps PA196.Program.sites n ⟨.at 25, seedRegisters⟩ ⟨.at 3692, registers⟩) :
    registers 3 = 0 ∧ registers 4 = 0 ∧ registers 5 = 0 ∧ registers 6 = 0 := by
  have seed : Holds (fun pc m => (certificate pc).testBit (encode m) = true)
      ⟨.at 25, seedRegisters⟩ := by
    simp [Holds, h25, seed_mask, seed_present]
  have reached := steps_preserve PA196.Program.sites
    (fun pc m => (certificate pc).testBit (encode m) = true) closed run seed
  have hm : site3692.testBit (encode (mask registers)) = true := by
    simpa [Holds, h3692] using reached
  let m : Fin 512 := ⟨encode (mask registers), encode_bound (mask registers)⟩
  have h3 := site3692_reg3_zero m hm
  have h4 := site3692_reg4_zero m hm
  have h5 := site3692_reg5_zero m hm
  have h6 := site3692_reg6_zero m hm
  change (encode (mask registers)).testBit ((3 : Fin 9) : Nat) = false at h3
  have hm3 : mask registers 3 = false := by simpa only [encode_testBit] using h3
  change (encode (mask registers)).testBit ((4 : Fin 9) : Nat) = false at h4
  have hm4 : mask registers 4 = false := by simpa only [encode_testBit] using h4
  change (encode (mask registers)).testBit ((5 : Fin 9) : Nat) = false at h5
  have hm5 : mask registers 5 = false := by simpa only [encode_testBit] using h5
  change (encode (mask registers)).testBit ((6 : Fin 9) : Nat) = false at h6
  have hm6 : mask registers 6 = false := by simpa only [encode_testBit] using h6
  exact ⟨by simpa [mask] using hm3, by simpa [mask] using hm4,
    by simpa [mask] using hm5, by simpa [mask] using hm6⟩

#print axioms seed_mask
#print axioms source_3692_zero_if_closed
end PA196ZeroMask
