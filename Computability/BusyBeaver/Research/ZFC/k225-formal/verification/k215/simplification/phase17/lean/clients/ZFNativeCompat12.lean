import BusyBeaver.ZFC.ZFNative

namespace SetTheory.BusyBeaver.ZFC.ZFNativeCompat12
open NativeTheory254 InternalOrd
universe u
variable {V : Type u}

theorem models (mem : V → V → Prop) (v : Nat → V) (h : ∀ f, ZFax_s f → Sat mem v f) :
    ZFAxioms mem ∧ (∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) ∧ Regular mem :=
  ZFNative.models_ZF mem v h

theorem native (mem : V → V → Prop) (v : Nat → V) (h : ∀ f, ZFax_s f → Sat mem v f) :
    ∀ f, NativeAx f → Sat mem v f := ZFNative.native_of_zf mem v h

theorem refutation (h : BProv NativeAx [] Form.fBot) : BProv ZFax_s [] Form.fBot :=
  ZFNative.zf_refutation_of_native h

theorem halt_zf
    (h : RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) :
    BProv ZFax_s [] Form.fBot := ZFNative.zf_refutation_of_halting h

theorem con_zf (hCon : ¬ BProv ZFax_s [] Form.fBot) :
    ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  ZFNative.nonhalting_of_zf_consistent hCon

theorem halt_zfc
    (h : RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) :
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  ZFNative.zfc_refutation_of_halting h

theorem con_zfc (hCon : ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot) :
    ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  ZFNative.nonhalting_of_zfc_consistent hCon
end SetTheory.BusyBeaver.ZFC.ZFNativeCompat12

#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.models
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.native
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.refutation
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.halt_zf
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.con_zf
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.halt_zfc
#print axioms SetTheory.BusyBeaver.ZFC.ZFNativeCompat12.con_zfc
