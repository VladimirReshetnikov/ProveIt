import BusyBeaver.ZFC.KDense221
import BusyBeaver.ZFC.KBoot221
import BusyBeaver.ZFC.KSites221
import BusyBeaver.ZFC.KEngine221
import BusyBeaver.ZFC.KUpper222

/-!
The 221-state machine's Lean endpoint: TM layer and program layer composed.

* `KBoot221.boot`: from the blank tape the machine reaches the dispatch configuration of the empty
  path with the boot registers (`nextproof = 3`, `param1 = 3`) and 167 spare register blocks.
* `KSites221.covered`: every decoder leaf of the 221's source passes the symbolic site check, so
  the machine simulates the source program (`KSim.halts_iff`, with K230's register lemmas, which
  hold for the 221's table by `KEngine221.tm221_box`).
* `KSource221.p221_boot_iff`: the source halts from the boot registers iff the code 1 is derivable
  in the 222/221 calculus `C222`.
* `KDense221.commutes`: the literal dense `Machine 221` is the K230-label table, relabelled.

`blank_halts_iff_c222` is the full equivalence. With `KUpper222.zf_refutation_of_c222`, halting
yields a refutation of ZF; the converse (a ZF refutation makes the code 1 derivable) is the lower
chain of the calculus, stated separately.
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint221

open KZip KTableCore KDenseBridge KDense221 KBoot221 LeanProofs.BoundedZFCConsistency

/-- Halting is preserved forward along a run: the machine is deterministic. -/
theorem halts_of_reach {M : TMN} {a b : Conf} (h : Reach M a b) (ha : Halts M a) : Halts M b := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨c, ⟨t, ht⟩, hc⟩ := ha
  by_cases hle : j ≤ t
  · have e : t = j + (t - j) := by omega
    rw [e, run_add, hj] at ht
    exact ⟨c, ⟨_, ht⟩, hc⟩
  · have e : j = t + (j - t) := by omega
    obtain ⟨m, hm⟩ : ∃ m, j - t = m + 1 := ⟨j - t - 1, by omega⟩
    rw [e, run_add, ht, hm] at hj
    simp [run, hc] at hj

theorem boot_rel : KSim.Rel KSource221.p221 ⟨[], L2K.bootRegs⟩ (zc 84 [true] bootRight) := by
  refine ⟨RegisterPathClean.clean_nil _, 181, List.replicate 167 1, by decide, by simp, ?_⟩
  rfl

/-- The sparse-label machine, from the blank tape, halts iff the 221's source halts from the boot
registers. -/
theorem sparse_iff_source :
    Halts tm221 (zc 0 [] []) ↔ RegisterPath.Halts KSource221.p221 ⟨[], L2K.bootRegs⟩ := by
  rw [KSim.halts_iff KEngine221.tm221_box KSites221.covered terminal boot_rel]
  exact ⟨halts_of_reach boot, Halts.of_reach boot⟩

/-- **The 221-state machine halts iff the code 1 is derivable in the 222/221 calculus.** -/
theorem blank_halts_iff_c222 : BlankHalts machine221 ↔ KCode222.C222 Code254.F :=
  (blank_iff commutes terminal).trans (sparse_iff_source.trans KSource221.p221_boot_iff)

/-- **If the 221-state machine halts, ZF is refutable.** -/
theorem zf_refutation_of_halts (h : BlankHalts machine221) : BProv ZFax_s [] Form.fBot :=
  KUpper222.zf_refutation_of_c222 (blank_halts_iff_c222.mp h)

/-- **If ZF is consistent, the 221-state machine runs forever.** -/
theorem nonhalting_of_zf_consistency (h : ¬ BProv ZFax_s [] Form.fBot) : ¬ BlankHalts machine221 :=
  fun hh => h (zf_refutation_of_halts hh)

#print axioms blank_halts_iff_c222
#print axioms zf_refutation_of_halts

end SetTheory.BusyBeaver.ZFC.KEndpoint221
