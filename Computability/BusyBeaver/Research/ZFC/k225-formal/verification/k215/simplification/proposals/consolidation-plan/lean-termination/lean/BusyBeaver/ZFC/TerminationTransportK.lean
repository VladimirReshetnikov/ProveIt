import BusyBeaver.ZFC.TerminationTransport
import BusyBeaver.ZFC.KZip
import BusyBeaver.ZFC.RegisterPath

/-!
Adapters for the exact KZip and RegisterPath interfaces at ProveIt commit
cbf94cb552a3b49509e0eee80e7455d4eb5974c6.

The completeness premise below is indispensable: RegisterPath.step = none
can also arise from exhausted decoder fuel.  KSim.sim_stop supplies this
premise from the existing coverage certificate.
-/
namespace SetTheory.BusyBeaver.ZFC.TerminationTransportK

private theorem path_run (p : RegisterPath.Program) (n : Nat) (c : RegisterPath.Configuration) :
    TerminationTransport.run (RegisterPath.step p) n c = RegisterPath.run p n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [TerminationTransport.run, RegisterPath.run]
    cases RegisterPath.step p c with
    | none => rfl
    | some c' => exact ih c'

private theorem zip_run (M : KZip.TMN) (n : Nat) (c : KZip.Conf) :
    TerminationTransport.run (KZip.step M) n c = KZip.run M n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [TerminationTransport.run, KZip.run]
    cases KZip.step M c with
    | none => rfl
    | some c' => exact ih c'

private theorem zip_halts (M : KZip.TMN) (c : KZip.Conf) :
    TerminationTransport.Halts (KZip.step M) c ↔ KZip.Halts M c := by
  simp only [TerminationTransport.Halts, zip_run, KZip.Halts, KZip.Reach]
  constructor
  · rintro ⟨n, c', hr, hs⟩; exact ⟨c', ⟨n, hr⟩, hs⟩
  · rintro ⟨c', ⟨n, hr⟩, hs⟩; exact ⟨n, c', hr, hs⟩

/-- Direct replacement for KEndpoint.halts_of_reach. -/
theorem halts_of_reach {M : KZip.TMN} {a b : KZip.Conf}
    (hr : KZip.Reach M a b) (hh : KZip.Halts M a) : KZip.Halts M b := by
  obtain ⟨n, hn⟩ := hr
  exact (zip_halts M b).mp ((zip_halts M a).mpr hh |>.at_reach ⟨n, by rwa [zip_run]⟩)

/-- Positive forward simulation, with literal source halting retained. -/
theorem halts_iff {p : RegisterPath.Program} {M : KZip.TMN}
    {R : RegisterPath.Configuration → KZip.Conf → Prop}
    (sim : ∀ {c c' T}, R c T → RegisterPath.step p c = some c' →
      ∃ T', R c' T' ∧ KZip.Reach1 M T T')
    (stop : ∀ {c T}, R c T → RegisterPath.AtHalt p c → KZip.Halts M T)
    (complete : ∀ {c}, RegisterPath.step p c = none → RegisterPath.AtHalt p c)
    {c T} (hR : R c T) : RegisterPath.Halts p c ↔ KZip.Halts M T := by
  have hp : RegisterPath.Halts p c ↔ TerminationTransport.Halts (RegisterPath.step p) c := by
    simp only [RegisterPath.Halts, TerminationTransport.Halts, path_run]
    constructor
    · rintro ⟨n, c', hr, d, hh⟩
      exact ⟨n, c', hr, by simp [RegisterPath.step, hh, RegisterPath.execute]⟩
    · rintro ⟨n, c', hr, hs⟩; exact ⟨n, c', hr, complete hs⟩
  refine hp.trans ((TerminationTransport.halts_iff (R := R) ?_ ?_ hR).trans (zip_halts M T))
  · intro c c' T hR hs
    obtain ⟨T', hr, n, hn⟩ := sim hR hs
    exact ⟨T', hr, n, by rwa [zip_run]⟩
  · intro c T hR hs
    exact (zip_halts M T).mpr (stop hR (complete hs))

#print axioms halts_iff
#print axioms halts_of_reach

end SetTheory.BusyBeaver.ZFC.TerminationTransportK
