import BusyBeaver.ZFC.KSeedDirect222
import BusyBeaver.ZFC.KLowerQHyp
import BusyBeaver.ZFC.KUpper222
import BusyBeaver.ZFC.KSim
import BusyBeaver.ZFC.KDenseBridge

/-!
The endpoint composition of the K-family machines, once for all of them.

A K machine's endpoint has five machine-specific inputs, and `blank_halts_iff_zfc_refutation`
composes them:

* the literal dense machine is its sparse K230-label table, relabelled (`KDenseBridge.blank_iff`);
* the table keeps K230's register routines (`KRuntimeCore.BoxLemmas`, from `KTape.boxLemmas`);
* from the blank tape the table reaches the dispatch configuration of the empty path with some
  boot registers `R0` (`nextproof = 3`, `param1 = 3` for the K230 boots; `nextproof = 4` for the
  215's);
* every decoder leaf of the source passes the symbolic site check (`KSim.Covered`), so the machine
  simulates the source (`KSim.halts_iff`);
* the source, from `R0`, halts iff the code 1 is derivable in the 222 calculus.

The calculus is machine-independent: `KUpper222.zf_refutation_of_c222` is the upper bound, and the
lower chain `c222_of_zf_refutation` is semantic. Take for the completeness theorem
`KEind222.c222_complete` the named formulas whose interpreted codes are derivable
(`DerivableNF`). A fresh-label named bundle gives every named relation, including literal
equality, Elliot Glazer's seed property on this original domain
(`seed_direct`, `formSeed_of_fullSeed`). The bisimulation quotient of its
tagged domain has a well-founded part satisfying ZF (`zf_consistent_of_formSeed`). So a ZF
refutation leaves no model, and the code 1 is derivable.
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint

open KZip KRuntimeCore KDenseBridge LeanProofs.BoundedZFCConsistency KSeed222 KIndisc222 KLower

/-- **Lower chain.** A refutation of ZF makes the code 1 derivable. -/
theorem c222_of_zf_refutation (hf : BProv ZFax_s [] Form.fBot) : KCode222.C222 Code254.F := by
  apply KEind222.c222_complete DerivableNF (fun _ h => h)
  intro D mem hirr hT e
  have hfull : FullSeed mem := ⟨hirr, seed_direct mem hT⟩
  exact zf_consistent_of_formSeed (formSeed_of_fullSeed hfull) hfull.irr (e 0) hf

/-- The 222 calculus derives the code 1 iff ZF is refutable. -/
theorem c222_iff_zf_refutation : KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨KUpper222.zf_refutation_of_c222, c222_of_zf_refutation⟩

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

section

variable {m : Nat} {D : Machine (m + 1)} {M : TMN} {ex : Nat → Nat} {p : RegisterPath.Program}
  {T : Conf} {R0 : RegisterPath.Registers} (hD : Commutes D M ex 230) (hH : ∀ b, M 230 b = none)
  (hB : BoxLemmas M) (hcov : KSim.Covered M p) (hboot : Reach M (zc (ex 0) [] []) T)
  (hrel : KSim.Rel p ⟨[], R0⟩ T)
  (hsrc : RegisterPath.Halts p ⟨[], R0⟩ ↔ KCode222.C222 Code254.F)
include hD hH hB hcov hboot hrel hsrc

/-- **A K machine halts iff the code 1 is derivable in the 222 calculus.** -/
theorem blank_halts_iff_c222 : BlankHalts D ↔ KCode222.C222 Code254.F := by
  rw [blank_iff hD hH, ← hsrc, KSim.halts_iff hB hcov hH hrel]
  exact ⟨halts_of_reach hboot, Halts.of_reach hboot⟩

/-- **A K machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts D ↔ BProv ZFCax_s [] Form.fBot :=
  ((blank_halts_iff_c222 hD hH hB hcov hboot hrel hsrc).trans c222_iff_zf_refutation).trans
    ConstructibleChoice.zf_refutation_iff_zfc_refutation

end

end SetTheory.BusyBeaver.ZFC.KEndpoint
