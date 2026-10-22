import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.ZFNative
import BusyBeaver.ZFC.WFTheory

/-! Typed checks for the moved model view, K215's semantic calibration, and
the original program clients. No literal K215 source/site proof is rebuilt. -/

namespace SetTheory.BusyBeaver.ZFC.ImportCutAudit

open InternalOrd

universe u

theorem model_view_unchanged {V : Type u} (mem : V → V → Prop) (v : Nat → V)
    (h : ∀ f, ZFax_s f → Sat mem v f) :
    ZFAxioms mem ∧ (∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) ∧ Regular mem :=
  ZFNative.models_ZF mem v h

theorem calibration_unchanged :
    KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  KEndpoint.c222_iff_zf_refutation

theorem legacy_program_unchanged
    (h : RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) :
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  ZFNative.zfc_refutation_of_halting h

#print axioms model_view_unchanged
#print axioms calibration_unchanged
#print axioms legacy_program_unchanged
#print axioms ZFNative.models_ZF
#print axioms KQ1ZF.zf_consistent
#print axioms ConstructibleChoice.zf_refutation_iff_zfc_refutation
#print axioms KEndpoint.blank_halts_iff_zfc_refutation
#print axioms WFTheory.native_consistency_iff_zf

end SetTheory.BusyBeaver.ZFC.ImportCutAudit
