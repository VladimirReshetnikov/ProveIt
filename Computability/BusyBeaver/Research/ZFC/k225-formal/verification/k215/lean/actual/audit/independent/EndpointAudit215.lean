import BusyBeaver.ZFC.KEndpoint215

/-!
Independent typed endpoint clients. This file assumes no theorem parameters or consistency
hypothesis. Compilation and axiom output are supplied separately by the assigned build lane.
-/
namespace EndpointAudit215

open SetTheory
open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open LeanProofs.BoundedZFCConsistency

theorem exact_working_state_count : KDense215.rows215.length = 215 :=
  KDense215.rows215_length

theorem blank_halts_exactly_when_zfc_has_a_finite_refutation :
    (∃ t : Nat, (KDense215.machine215.run t).state = none) ↔
      BProv ZFCax_s [] Form.fBot :=
  KEndpoint215.blank_halts_iff_zfc_refutation

theorem nonhalting_exactly_when_zfc_is_consistent :
    (¬ ∃ t : Nat, (KDense215.machine215.run t).state = none) ↔
      ¬ BProv ZFCax_s [] Form.fBot :=
  KEndpoint215.nonhalting_iff_zfc_consistency

#print axioms blank_halts_exactly_when_zfc_has_a_finite_refutation
#print axioms nonhalting_exactly_when_zfc_is_consistent

end EndpointAudit215
