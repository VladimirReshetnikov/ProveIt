import BusyBeaver.ZFC.L2Root254
import BusyBeaver.ZFC.QuotientZF0

/-!
The actual 219-node structured program inherits the one-way ZF0 calibration.
The initial register file has nextproof = 2 and every other register zero.
This uses the proved L2 equivalence and the actual quotient-model construction.
No identification with the different literal Prog254 tree or the binary
machine is assumed. The converse and Foundation/Choice transport are separate.
-/

namespace SetTheory.BusyBeaver.ZFC.ProgramZF0

/-- A refutation of ZF without Foundation or Choice forces the actual
structured register program to halt from its specified initial registers. -/
theorem program_halts_of_zf0_refutation
    (hf : BProv PSCCalibration.ZF0Ax [] .fBot) :
    RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  L2.program_halts_iff.mpr (QuotientZF0.c254_of_zf0_refutation hf)

/-- Contrapositive at the structured-program layer, without a binary simulation. -/
theorem zf0_consistent_of_program_nonhalting
    (h : ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) :
    ¬ BProv PSCCalibration.ZF0Ax [] .fBot :=
  fun hf => h (program_halts_of_zf0_refutation hf)

end SetTheory.BusyBeaver.ZFC.ProgramZF0
