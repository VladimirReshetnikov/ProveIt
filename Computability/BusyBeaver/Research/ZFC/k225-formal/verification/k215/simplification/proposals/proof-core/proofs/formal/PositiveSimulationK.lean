import PositiveSimulation
import BusyBeaver.ZFC.KZip
import BusyBeaver.ZFC.RMBisim

/-!
Exact adapters for applying the existing FM215 positive simulation theorem
inside the current K-family runtime.  No new machine-specific premise is added.
This file is an architectural extraction: it shortens the KSim client, but adds
adapter source to its closure.  It is not a total-source-size improvement alone.
-/
namespace SetTheory.BusyBeaver.ZFC.PositiveSimulationK

private theorem path_run (p : RegisterPath.Program) (n : Nat) (c : RegisterPath.Configuration) :
    PositiveSimulation.run (RegisterPath.step p) n c = RegisterPath.run p n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PositiveSimulation.run, RegisterPath.run]
    cases RegisterPath.step p c with
    | none => rfl
    | some c' => exact ih c'

private theorem zip_run (M : KZip.TMN) (n : Nat) (c : KZip.Conf) :
    PositiveSimulation.run (KZip.step M) n c = KZip.run M n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PositiveSimulation.run, KZip.run]
    cases KZip.step M c with
    | none => rfl
    | some c' => exact ih c'

private theorem zip_halts (M : KZip.TMN) (c : KZip.Conf) :
    PositiveSimulation.Halts (KZip.step M) c ↔ KZip.Halts M c := by
  simp only [PositiveSimulation.Halts, zip_run, KZip.Halts, KZip.Reach]
  constructor
  · rintro ⟨n, c', hr, hs⟩; exact ⟨c', ⟨n, hr⟩, hs⟩
  · rintro ⟨c', ⟨n, hr⟩, hs⟩; exact ⟨n, c', hr, hs⟩

/-- The existing generic theorem, specialized to the exact current K-family
run conventions. Literal source halting is retained: decoder exhaustion is
excluded by `complete`, which current KSim supplies from site coverage. -/
theorem halts_iff {p : RegisterPath.Program} {M : KZip.TMN}
    {R : RegisterPath.Configuration → KZip.Conf → Prop}
    (sim : ∀ {c c' T}, R c T → RegisterPath.step p c = some c' →
      ∃ T', R c' T' ∧ KZip.Reach1 M T T')
    (stop : ∀ {c T}, R c T → RegisterPath.AtHalt p c → KZip.Halts M T)
    (complete : ∀ {c}, RegisterPath.step p c = none → RegisterPath.AtHalt p c)
    {c T} (hR : R c T) : RegisterPath.Halts p c ↔ KZip.Halts M T := by
  have hp : RegisterPath.Halts p c ↔ PositiveSimulation.Halts (RegisterPath.step p) c := by
    simp only [RegisterPath.Halts, PositiveSimulation.Halts, path_run]
    constructor
    · rintro ⟨n, c', hr, hh⟩; exact ⟨n, c', hr, RMBisim.atHalt_step hh⟩
    · rintro ⟨n, c', hr, hs⟩; exact ⟨n, c', hr, complete hs⟩
  refine hp.trans ((PositiveSimulation.halts_iff (R := R) ?_ ?_ hR).trans (zip_halts M T))
  · intro c c' T hR hs
    obtain ⟨T', hr, n, hn⟩ := sim hR hs
    exact ⟨T', hr, n, by rwa [zip_run]⟩
  · intro c T hR hs
    exact (zip_halts M T).mpr (stop hR (complete hs))

#print axioms halts_iff
end SetTheory.BusyBeaver.ZFC.PositiveSimulationK
