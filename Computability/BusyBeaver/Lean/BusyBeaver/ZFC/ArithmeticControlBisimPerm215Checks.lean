import BusyBeaver.ZFC.ArithmeticControlBisimPerm215

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisimPerm215
open ArithmeticControlBisim (Vec entryOK)
open ArithmeticControlFile (liveValue)

example : certSize = 2850 := rfl
example : fuel = 6 := rfl
example : zeros.length = 9 := rfl
example : zeros ≠ ([] : Vec) := by decide
example : rootEntry.s0 = 2 ∧ rootEntry.s1 = 1 := ⟨rfl, rfl⟩
example : cert 0 = some rootEntry := cert_zero
example : entryOK ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
    cert fuel certSize 2849 = true := check_all 2849 (by decide)
example : PackedTables.slot packedCert 2849 96 < 2 ^ 86 := reserved_bits 2849 (by decide)
example : cert 2850 = none := cert_outside 2850 (by decide)

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward (x : V)
    (h : ∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) :
    ∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0 := (halts_iff x).mp h

theorem backward (x : V)
    (h : ∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0) :
    ∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0 := (halts_iff x).mpr h
end Model

#print axioms packedCert_bound
#print axioms check_all
#print axioms reserved_bits
#print axioms entry_diagonal_offsets
#print axioms cert_outside
#print axioms cert_zero
#print axioms root_controls
#print axioms root_offsets
#print axioms halts_iff
#print axioms forward
#print axioms backward
end SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215Checks
