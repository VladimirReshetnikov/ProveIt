import BusyBeaver.ZFC.RuntimeInstancePrefix246
import BusyBeaver.ZFC.BootstrapFrame246
import BusyBeaver.ZFC.SitesPrefix246

/-!
Closed external calibration of the exact contextual-fold246 blank machine.
The intended proof joins every actual decoder case, the entire 410735-step
startup, the whole-tape simulation and the independently calibrated seed.
The finite-prefix lemma and composition follow BinaryPerm252; the original
proof-search program and simulation are attributed to Mira-Cult, Jeff
Ketchersid and Andrew James Wade. This is an external Lean metatheorem,
not an object-theory PA proof or an unconditional consistency assertion.
-/
namespace SetTheory.BusyBeaver.ZFC.BinaryPrefix246

open RuntimePerm252 RuntimeInstancePrefix246

/-- The literal Core blank run, starting at state0, head0 and the empty tape. -/
def BlankHalts {states : Nat} (M : Machine states) : Prop :=
  ∃ t, (M.run t).state = none

theorem blank_initial_config :
    initial 246 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 246) := rfl

theorem actual_coverage : Covered Prog254.program :=
  covered_of_allSites Prog254.program ActualTree254.tree
    ActualTree254.tree_eq SitesPrefix246.all_sites

theorem boot_related :
    Related Prog254.program LogicalSeed246.initial (machinePrefix246.run 410735) := by
  refine ⟨LogicalSeed246.root_clean, 181, BootstrapFrame246.spares,
    BootstrapFrame246.spares_nonempty, ?_⟩
  exact BootstrapFrame246.bootstrap_frame

/-- Halting is unchanged by removing a finite initial segment of the actual run. -/
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

theorem blank_halts_iff_register :
    BlankHalts machinePrefix246 ↔ RegisterPath.Halts Prog254.program LogicalSeed246.initial := by
  have h := register_halts_iff_binary Prog254.program actual_coverage LogicalSeed246.initial
    (machinePrefix246.run 410735) boot_related
  exact (h.trans (blank_after_prefix_iff machinePrefix246 410735)).symm

theorem blank_halts_iff_zf_refutation :
    BlankHalts machinePrefix246 ↔ BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_register.trans LogicalSeed246.halts_iff_zf_refutation

theorem blank_halts_iff_zfc_refutation :
    BlankHalts machinePrefix246 ↔ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_register.trans LogicalSeed246.halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ BlankHalts machinePrefix246) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr blank_halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts machinePrefix246) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.BinaryPrefix246
