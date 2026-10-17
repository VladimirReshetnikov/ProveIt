import BusyBeaver.ZFC.SitesPerm252
import BusyBeaver.ZFC.RuntimeInstancePerm252
import BusyBeaver.ZFC.BootstrapFramePerm252
import BusyBeaver.ZFC.Permutation252Program
import BusyBeaver.ZFC.WFTheory
import BusyBeaver.ZFC.Code254Proof

/-!
The literal permutation252 blank machine and the exact native theory.

This composition uses the closed all-sites certificate against the actual
Prog254 decoder tree, the checked 82,552-transition blank bootstrap, the
whole-frame runtime equivalence and the safe zero-root program endpoint.
No coverage or register-operation premise remains in the endpoint statements.

Attribution: Mira-Cult's original machine, Jeff's verification and Wade's
compiler framework at upstream297ab8df7e5de329605c3875b4934643b371a5e3;
mira-emmy's public253 reduction at PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856. The independently found permutation
candidate has old-label SHA256
939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713.
Its canonical table is TablePerm252:252 working states, start0, halt none.

The native theory here is exactly NativeTheory254.NativeAx. Its checked
well-founded-part interpretation also gives the stated full-ZF comparison,
including Foundation. ChoiceCalibration254 and BinaryZFC252 extend this to
the external standard-ZFC comparison. Internal arithmetic formalization in PA
remains separate.

This source must be checked only after SitesPerm252's full closed certificate
has passed. Source existence alone is not a completed kernel verification.
-/

namespace SetTheory.BusyBeaver.ZFC.BinaryPerm252

open RegisterPath RegisterPathClean Permutation252Frame
open RuntimePerm252 RuntimeInstancePerm252

/-- Halting of the existing Core blank run, with its actual initial state,
head0 and empty tape. There is no alternative chosen start configuration. -/
def BlankHalts {states : Nat} (M : Machine states) : Prop :=
  ∃ t, (M.run t).state = none

theorem blank_initial_config :
    initial 252 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 252) := rfl

theorem actual_coverage : Covered Prog254.program :=
  covered_of_allSites Prog254.program ActualTree254.tree
    ActualTree254.tree_eq SitesPerm252.all_sites

theorem boot_related : Related Prog254.program zeroRoot (machinePerm252.run 82552) := by
  refine ⟨clean_nil Prog254.program, 40, BootPerm252.bootSparesPerm252, ?_⟩
  simpa only [SitePerm252.dispatch, BootstrapFramePerm252.dispatchPerm252] using
    BootstrapFramePerm252.boot_dispatch_frame

/-- Adding or removing an actual finite binary prefix preserves eventual
halting, including halting that might occur inside that prefix. -/
theorem blank_after_prefix_iff {states : Nat} (M : Machine states) (N : Nat) :
    BinaryHalts M (M.run N) ↔ BlankHalts M := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨N + t, by simpa only [Machine.run_add_eq_runFrom] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have he : M.run (N + t) = M.run (t + N) := by rw [Nat.add_comm N t]
    have hh := M.runFrom_of_halted (M.run t) ht N
    rw [Machine.run_add_eq_runFrom, Machine.run_add_eq_runFrom, hh] at he
    rw [he]
    exact ht

/-- The standard blank binary machine and the actual literal register
program halt together. All local coverage checks are closed theorems. -/
theorem blank_halts_iff_register :
    BlankHalts machinePerm252 ↔ RegisterPath.Halts Prog254.program zeroRoot := by
  have h := register_halts_iff_binary Prog254.program actual_coverage zeroRoot
    (machinePerm252.run 82552) boot_related
  exact (h.trans (blank_after_prefix_iff machinePerm252 82552)).symm

theorem blank_halts_iff_c254 :
    BlankHalts machinePerm252 ↔ Code254.C254 Code254.F :=
  blank_halts_iff_register.trans Permutation252Program.literal_zero_halts_iff_c254

/-- An external natural-number witness accepted by the exact finite proof
checker. This statement does not assert its representation inside PA. -/
theorem blank_halts_iff_checked_refutation :
    BlankHalts machinePerm252 ↔ ∃ code, Code254Proof.check code Code254.F = true :=
  blank_halts_iff_c254.trans (Code254Proof.c254_iff_checked Code254.F)

theorem blank_halts_iff_native_refutation :
    BlankHalts machinePerm252 ↔ BProv NativeTheory254.NativeAx [] Form.fBot :=
  blank_halts_iff_register.trans
    Permutation252Program.literal_zero_halts_iff_native_refutation

theorem blank_halts_iff_zf_refutation :
    BlankHalts machinePerm252 ↔ BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_c254.trans WFTheory.c254_refutation_iff_zf

theorem nonhalting_iff_no_c254_refutation :
    (¬ BlankHalts machinePerm252) ↔ ¬ Code254.C254 Code254.F :=
  not_congr blank_halts_iff_c254

theorem nonhalting_iff_no_checked_refutation :
    (¬ BlankHalts machinePerm252) ↔
      ¬ ∃ code, Code254Proof.check code Code254.F = true :=
  not_congr blank_halts_iff_checked_refutation

theorem nonhalting_iff_native_consistency :
    (¬ BlankHalts machinePerm252) ↔ ¬ BProv NativeTheory254.NativeAx [] Form.fBot :=
  not_congr blank_halts_iff_native_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ BlankHalts machinePerm252) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr blank_halts_iff_zf_refutation

#print axioms blank_initial_config
#print axioms actual_coverage
#print axioms boot_related
#print axioms blank_after_prefix_iff
#print axioms blank_halts_iff_register
#print axioms blank_halts_iff_c254
#print axioms blank_halts_iff_checked_refutation
#print axioms blank_halts_iff_native_refutation
#print axioms blank_halts_iff_zf_refutation
#print axioms nonhalting_iff_no_c254_refutation
#print axioms nonhalting_iff_no_checked_refutation
#print axioms nonhalting_iff_native_consistency
#print axioms nonhalting_iff_zf_consistency

end SetTheory.BusyBeaver.ZFC.BinaryPerm252
