import BusyBeaver.ZFC.RuntimeInstanceRotation240
import BusyBeaver.ZFC.BootstrapFrameRotation240
import BusyBeaver.ZFC.SitesRotation240
import BusyBeaver.ZFC.CalibratedRotation240

/-!
External calibration of the literal rotation240 machine on the blank tape.
The proof combines complete decoder-site coverage, the 409691-step whole-tape
startup frame, the positive runtime simulation and the calibrated rotated
register source. The statements equate halting with ZF/ZFC refutation and
nonhalting with consistency. They are external Lean statements, not proofs
formalized inside PA or assertions of unconditional nonhalting.
The original proof-search program, framework and reductions retain the
attribution of the imported proofs.
-/
namespace SetTheory.BusyBeaver.ZFC.BinaryRotation240

open RuntimePerm252 RuntimeInstanceRotation240

/-- The actual blank Core run at state0, head0, on the empty tape. -/
def BlankHalts {states : Nat} (M : Machine states) : Prop :=
  ∃ t, (M.run t).state = none

theorem blank_initial_config :
    initial 240 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 240) := rfl

theorem actual_coverage : Covered SourceRotation240.program :=
  covered_of_allSites SourceRotation240.program TreeRotation240.tree
    TreeRotation240.tree_eq SitesRotation240.all_sites

theorem boot_related :
    Related SourceRotation240.program LogicalSeed246.initial
      (machineRotation240.run 409691) := by
  refine ⟨RegisterPathClean.clean_nil SourceRotation240.program, 181,
    BootstrapFrameRotation240.spares, BootstrapFrameRotation240.spares_nonempty, ?_⟩
  exact BootstrapFrameRotation240.bootstrap_frame

/-- Halting is unchanged by removal of any finite prefix of the actual run. -/
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

theorem blank_halts_iff_rotation_register :
    BlankHalts machineRotation240 ↔
      RegisterPath.Halts SourceRotation240.program LogicalSeed246.initial := by
  have h := register_halts_iff_binary SourceRotation240.program actual_coverage
    LogicalSeed246.initial (machineRotation240.run 409691) boot_related
  exact (h.trans (blank_after_prefix_iff machineRotation240 409691)).symm

theorem blank_halts_iff_zf_refutation :
    BlankHalts machineRotation240 ↔ BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_rotation_register.trans CalibratedRotation240.halts_iff_zf_refutation

theorem blank_halts_iff_zfc_refutation :
    BlankHalts machineRotation240 ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_rotation_register.trans CalibratedRotation240.halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ BlankHalts machineRotation240) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr blank_halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts machineRotation240) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.BinaryRotation240
