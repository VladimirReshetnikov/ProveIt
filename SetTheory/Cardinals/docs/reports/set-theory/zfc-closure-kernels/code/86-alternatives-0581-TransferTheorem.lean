import BusyBeaver.ZFC.RuntimePerm252

/-!
Reusable final composition for any candidate binary table.
Status: source draft, independently reviewed, NOT compiled in this environment.
The imported positive-segment theorem already exists in the pinned development.
All candidate-specific and logical-calibration assumptions remain explicit.
-/
namespace SetTheory.BusyBeaver.ZFC.CandidateTransfer
open RuntimePerm252
universe u

def BlankHalts {n : Nat} (M : Machine n) : Prop :=
  ∃ t, (M.run t).state = none

theorem after_prefix_iff {n : Nat} (M : Machine n) (N : Nat) :
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

/-- Small generic endpoint: no state bound, simulation, seed or calibration
is inferred by the composition itself. -/
theorem nonhalting_iff_consistency {A : Type u} {n : Nat}
    (M : Machine n) (next : A → Option A) (terminal : A → Prop)
    (R : A → Config n → Prop) (a0 : A) (N : Nat) (Refutation : Prop)
    (sim : PositiveSimulation M next terminal R)
    (boot : R a0 (M.run N))
    (calibration : AbstractHalts next terminal a0 ↔ Refutation) :
    (¬ BlankHalts M) ↔ ¬ Refutation := by
  have runtime : AbstractHalts next terminal a0 ↔ BlankHalts M :=
    (RuntimePerm252.halts_iff sim a0 (M.run N) boot).trans (after_prefix_iff M N)
  exact not_congr (runtime.symm.trans calibration)

#print axioms after_prefix_iff
#print axioms nonhalting_iff_consistency
end SetTheory.BusyBeaver.ZFC.CandidateTransfer
