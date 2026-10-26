import DiophantineConsistency.DecimalMachineZFC

/-! Focused checks for the actual decimal machine endpoint and its axiom boundary. -/

namespace DiophantineConsistency.DecimalMachineZFCChecks

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency

example :
    (¬ KDenseBridge.BlankHalts DecimalMachine215.machine) ↔
      ¬ BProv ZFCax_s [] Form.fBot := DecimalMachineZFC.blank_nonhalting_iff_conZFC

example : ConZFC → ¬ KDenseBridge.BlankHalts DecimalMachine215.machine :=
  DecimalMachineZFC.blank_nonhalting_iff_conZFC.mpr

example : KDenseBridge.BlankHalts DecimalMachine215.machine → ¬ ConZFC := by
  intro hhalts hcon
  exact hcon (DecimalMachineZFC.blank_halts_iff_zfc_refutation.mp hhalts)

#print axioms DecimalMachine215.blank_halts_iff_dense
#print axioms KEndpoint215.blank_halts_iff_zfc_refutation
#print axioms DecimalMachineZFC.blank_halts_iff_zfc_refutation
#print axioms DecimalMachineZFC.blank_nonhalting_iff_conZFC

end DiophantineConsistency.DecimalMachineZFCChecks
