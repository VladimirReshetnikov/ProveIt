import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KDense217
import BusyBeaver.ZFC.KBoot217
import BusyBeaver.ZFC.KSites217
import BusyBeaver.ZFC.SeedDom

/-!
**The 217-state machine halts iff ZFC is inconsistent.**

The machine-specific inputs of `KEndpoint.blank_halts_iff_zfc_refutation`:

* `KDense217.commutes`: the literal dense `Machine 217` is the K230-label table, relabelled.
* `tm217_box`: the table agrees with K230 on the rows the register routines read and
  ends the increment with the 219's bypass `198/0 → 1 L 40`, so K230's register lemmas hold for it.
* `KBoot217.boot`: from the blank tape the table reaches the dispatch configuration of the empty
  path with the boot registers (`nextproof = 3`, `param1 = 3`) and 130 spare register blocks.
* `KSites217.covered`: every decoder leaf of the 217's source passes the symbolic site check.
* `p217_boot_iff`: the source halts from the boot registers iff `dagDom`, iterated, does
  (`KSource217`), iff Source 149's dominated enumerator halts from the seed
  (`L2Dom.dagDom_seed_iff`), iff the code 1 is derivable in `C222`: the enumerator compiles
  derivations of the dominated calculus `KCodeDom.CDom`, which derives exactly `C222`'s codes
  (`DomRho8.rho8_all`).
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint217

open KZip KTableCore KDenseBridge KDense217 KBoot217 KTape LeanProofs.BoundedZFCConsistency

theorem tm217_box : KRuntimeCore.BoxLemmas tm217 := boxLemmas (by decide) (.inr rfl)

theorem boot_rel : KSim.Rel KSource217.p217 ⟨[], L2K.bootRegs⟩ (zc 84 [true] bootRight) := by
  refine ⟨RegisterPathClean.clean_nil _, 144, List.replicate 130 1, by decide, by simp, ?_⟩
  rfl

/-- **Program layer.** The 217's source halts from the boot registers iff the code 1 is
derivable. -/
theorem p217_boot_iff :
    RegisterPath.Halts KSource217.p217 ⟨[], L2K.bootRegs⟩ ↔ KCode222.C222 Code254.F :=
  (KSource217.p217_halts_iff _).trans ((KSource217.path_iff_iter _).trans L2Dom.dagDom_seed_iff)

/-- **The 217-state machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts machine217 ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation commutes terminal tm217_box KSites217.covered boot boot_rel
    p217_boot_iff

/-- **The 217-state machine runs forever iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency : (¬ BlankHalts machine217) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.KEndpoint217
