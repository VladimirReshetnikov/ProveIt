import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KDense218
import BusyBeaver.ZFC.KBoot218
import BusyBeaver.ZFC.KSites218
import BusyBeaver.ZFC.Dag219Equiv

/-!
**The 218-state machine halts iff ZFC is inconsistent.**

The machine-specific inputs of `KEndpoint.blank_halts_iff_zfc_refutation`:

* `KDense218.commutes`: the literal dense `Machine 218` is the K230-label table, relabelled.
* `tm218_box`: the table agrees with K230 on the rows the register routines read and
  ends the increment with the 219's bypass `198/0 → 1 L 40`, so K230's register lemmas hold for it.
* `KBoot218.boot`: from the blank tape the table reaches the dispatch configuration of the empty
  path with the boot registers (`nextproof = 3`, `param1 = 3`) and 130 spare register blocks.
* `KSites218.covered`: every decoder leaf of the 218's source passes the symbolic site check.
* `p218_boot_iff`: the source halts from the boot registers iff `dag219`, iterated, does
  (`KSource218`), iff `dag222` does (`Dag219.iter_iff`), iff the code 1 is derivable in the 222
  calculus `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint218

open KZip KTableCore KDenseBridge KDense218 KBoot218 KTape LeanProofs.BoundedZFCConsistency

theorem tm218_box : KRuntimeCore.BoxLemmas tm218 := boxLemmas (by decide) (.inr rfl)

theorem boot_rel : KSim.Rel KSource218.p218 ⟨[], L2K.bootRegs⟩ (zc 84 [true] bootRight) := by
  refine ⟨RegisterPathClean.clean_nil _, 144, List.replicate 130 1, by decide, by simp, ?_⟩
  rfl

/-- **Program layer.** The 218's source halts from the boot registers iff the code 1 is
derivable. -/
theorem p218_boot_iff :
    RegisterPath.Halts KSource218.p218 ⟨[], L2K.bootRegs⟩ ↔ KCode222.C222 Code254.F :=
  (KSource218.p218_halts_iff _).trans ((KSource218.path_iff_iter _).trans Dag219.seed_iff)

/-- **The 218-state machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts machine218 ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation commutes terminal tm218_box KSites218.covered boot boot_rel
    p218_boot_iff

/-- **The 218-state machine runs forever iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency : (¬ BlankHalts machine218) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.KEndpoint218
