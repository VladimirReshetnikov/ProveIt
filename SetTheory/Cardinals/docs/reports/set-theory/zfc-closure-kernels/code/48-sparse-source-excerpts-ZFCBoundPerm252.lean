import BusyBeaver.ZFC.BinaryPerm252
import BusyBeaver.ZFC.ZFNative
import BusyBeaver.ZFC.QuotientZF0

/-!
Standard-theory bounds for the literal 252-state blank machine.

The direct well-founded-part interpretation and the internal rank construction
identify blank halting with ordinary ZF refutation, including Foundation and
Power. The endpoint includes the complete bootstrap and decoder certificate.

Thus blank nonhalting is equivalent to Con(ZF), and follows from Con(ZFC).
Removing Choice from finite ZFC refutations remains necessary to close the
full standard-ZFC equivalence. These are Lean metatheorems; formalization of
the final comparison in PA is separate.
-/

namespace SetTheory.BusyBeaver.ZFC.ZFCBoundPerm252
open BinaryPerm252

/-- A finite ZF0 refutation makes the actual blank machine halt. -/
theorem blank_halts_of_zf0_refutation
    (h : BProv PSCCalibration.ZF0Ax [] Form.fBot) : BlankHalts machinePerm252 :=
  blank_halts_iff_c254.mpr (QuotientZF0.c254_of_zf0_refutation h)

/-- Nonhalting of the actual blank machine implies consistency of ZF0. -/
theorem zf0_consistent_of_blank_nonhalting (h : ¬ BlankHalts machinePerm252) :
    ¬ BProv PSCCalibration.ZF0Ax [] Form.fBot :=
  fun hf => h (blank_halts_of_zf0_refutation hf)

/-- Halting of the actual blank machine supplies a finite ZF refutation. -/
theorem zf_refutation_of_blank_halting (h : BlankHalts machinePerm252) :
    BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_zf_refutation.mp h

/-- Halting of the actual blank machine supplies a finite ZFC refutation. -/
theorem zfc_refutation_of_blank_halting (h : BlankHalts machinePerm252) :
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BProv_theory_mono (fun _ hf => Or.inl hf) (zf_refutation_of_blank_halting h)

/-- Con(ZF) implies that the actual 252-state blank machine never halts. -/
theorem blank_nonhalting_of_zf_consistent (h : ¬ BProv ZFax_s [] Form.fBot) :
    ¬ BlankHalts machinePerm252 :=
  fun hh => h (zf_refutation_of_blank_halting hh)

/-- Con(ZFC) implies that the actual 252-state blank machine never halts. -/
theorem blank_nonhalting_of_zfc_consistent
    (h : ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot) :
    ¬ BlankHalts machinePerm252 :=
  fun hh => h (zfc_refutation_of_blank_halting hh)

#print axioms blank_halts_of_zf0_refutation
#print axioms zf0_consistent_of_blank_nonhalting
#print axioms zf_refutation_of_blank_halting
#print axioms zfc_refutation_of_blank_halting
#print axioms blank_nonhalting_of_zf_consistent
#print axioms blank_nonhalting_of_zfc_consistent

end SetTheory.BusyBeaver.ZFC.ZFCBoundPerm252

