import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KDense221
import BusyBeaver.ZFC.KBoot221
import BusyBeaver.ZFC.KSites221

/-!
**The 221-state machine halts iff ZFC is inconsistent.**

The machine-specific inputs of `KEndpoint.blank_halts_iff_zfc_refutation`:

* `KDense221.commutes`: the literal dense `Machine 221` is the K230-label table, relabelled.
* `tm221_box`: the table agrees with K230 on the rows the register routines read and
  ends the increment as K230 does, so K230's register lemmas hold for it.
* `KBoot221.boot`: from the blank tape the table reaches the dispatch configuration of the empty
  path with the boot registers (`nextproof = 3`, `param1 = 3`) and 167 spare register blocks.
* `KSites221.covered`: every decoder leaf of the 221's source passes the symbolic site check.
* `KSource221.p221_boot_iff`: the source halts from the boot registers iff the code 1 is derivable
  in the 222 calculus `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint221

open KZip KTableCore KDenseBridge KDense221 KBoot221 KTape LeanProofs.BoundedZFCConsistency

theorem tm221_box : KRuntimeCore.BoxLemmas tm221 := boxLemmas (by decide) (.inl ⟨rfl, rfl, rfl⟩)

theorem boot_rel : KSim.Rel KSource221.p221 ⟨[], L2K.bootRegs⟩ (zc 84 [true] bootRight) := by
  refine ⟨RegisterPathClean.clean_nil _, 181, List.replicate 167 1, by decide, by simp, ?_⟩
  rfl

/-- **The 221-state machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts machine221 ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation commutes terminal tm221_box KSites221.covered boot boot_rel
    KSource221.p221_boot_iff

/-- **The 221-state machine runs forever iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency : (¬ BlankHalts machine221) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.KEndpoint221
