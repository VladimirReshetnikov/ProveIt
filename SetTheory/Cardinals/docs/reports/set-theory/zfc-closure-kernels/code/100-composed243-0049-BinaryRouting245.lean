import BusyBeaver.ZFC.RuntimeInstanceRouting245
import BusyBeaver.ZFC.BootstrapFrameRouting245
import BusyBeaver.ZFC.SitesRouting245
import BusyBeaver.ZFC.BisimRouting245

/-!
Closed external calibration of the literal routed245 machine once the actual
whole-tree coverage and complete blank startup interfaces are supplied.
This source template requires SitesRouting245.all_sites and the final
BootstrapFrameRouting245.bootstrap_frame theorem. It does not define either
as an axiom or select an unproved object. The original proof-search program,
framework and reductions retain the attribution of the imported proofs.
The result is an external Lean refutation/consistency equivalence, not an
internal PA theorem or an unconditional nonhalting assertion.
-/
namespace SetTheory.BusyBeaver.ZFC.BinaryRouting245

open RuntimePerm252 RuntimeInstanceRouting245

/-- The actual blank Core run at state0, head0, on the empty tape. -/
def BlankHalts {states : Nat} (M : Machine states) : Prop :=
  ∃ t, (M.run t).state = none

theorem blank_initial_config :
    initial 245 = ({ state := some ⟨0, by decide⟩, head := 0, tape := [] } : Config 245) := rfl

theorem actual_coverage : Covered ProgramRouting245.program :=
  covered_of_allSites ProgramRouting245.program TreeRouting245.tree
    TreeRouting245.tree_eq SitesRouting245.all_sites

theorem boot_related :
    Related ProgramRouting245.program LogicalSeed246.initial
      (machineRouting245.run 407915) := by
  refine ⟨RegisterPathClean.clean_nil ProgramRouting245.program, 181,
    BootstrapFrameRouting245.spares, BootstrapFrameRouting245.spares_nonempty, ?_⟩
  exact BootstrapFrameRouting245.bootstrap_frame

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

/-- Bisimulation is used at the same calibrated register function, empty path. -/
theorem routed_seed_halts_iff_original :
    RegisterPath.Halts ProgramRouting245.program LogicalSeed246.initial ↔
      RegisterPath.Halts Prog254.program LogicalSeed246.initial :=
  BisimRouting245.program_halts_iff LogicalSeed246.registers

theorem blank_halts_iff_routed_register :
    BlankHalts machineRouting245 ↔
      RegisterPath.Halts ProgramRouting245.program LogicalSeed246.initial := by
  have h := register_halts_iff_binary ProgramRouting245.program actual_coverage
    LogicalSeed246.initial (machineRouting245.run 407915) boot_related
  exact (h.trans (blank_after_prefix_iff machineRouting245 407915)).symm

theorem blank_halts_iff_register :
    BlankHalts machineRouting245 ↔ RegisterPath.Halts Prog254.program LogicalSeed246.initial :=
  blank_halts_iff_routed_register.trans routed_seed_halts_iff_original

theorem blank_halts_iff_zf_refutation :
    BlankHalts machineRouting245 ↔ BProv ZFax_s [] Form.fBot :=
  blank_halts_iff_register.trans LogicalSeed246.halts_iff_zf_refutation

theorem blank_halts_iff_zfc_refutation :
    BlankHalts machineRouting245 ↔
      BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  blank_halts_iff_register.trans LogicalSeed246.halts_iff_zfc_refutation

theorem nonhalting_iff_zf_consistency :
    (¬ BlankHalts machineRouting245) ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr blank_halts_iff_zf_refutation

theorem nonhalting_iff_zfc_consistency :
    (¬ BlankHalts machineRouting245) ↔
      ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.BinaryRouting245
