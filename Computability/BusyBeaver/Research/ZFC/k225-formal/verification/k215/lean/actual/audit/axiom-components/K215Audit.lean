import BusyBeaver.ZFC.KEndpoint215

namespace K215Audit

open SetTheory SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LeanProofs.BoundedZFCConsistency

-- Explicit closed clients preserve the exact dense machine and ZFC proof predicate.
def denseMachine : Machine 215 := KDense215.machine215

theorem dense_table_length : KDense215.rows215.length = 215 :=
  KDense215.rows215_length

theorem blank_halts_exact :
    KDenseBridge.BlankHalts denseMachine ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint215.blank_halts_iff_zfc_refutation

theorem nonhalting_exact :
    (¬ KDenseBridge.BlankHalts denseMachine) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  KEndpoint215.nonhalting_iff_zfc_consistency

#print axioms KEndpoint215.blank_halts_iff_zfc_refutation
#print axioms KEndpoint215.nonhalting_iff_zfc_consistency
#print axioms KDense215.commutes
#print axioms KBoot215.boot
#print axioms KSites215.covered
#print axioms KEndpoint215.p215_boot_iff
#print axioms blank_halts_exact
#print axioms nonhalting_exact

end K215Audit
