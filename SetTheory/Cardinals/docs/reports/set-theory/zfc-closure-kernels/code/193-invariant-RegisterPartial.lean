import BusyBeaver.ZFC.RegisterPath
import BusyBeaver.ZFC.TerminalDrain

/-! Explicitly keep literal source halting distinct from failed decoding.
`halts_iff` requires evidence that every stuck configuration is a halt leaf. -/

namespace SetTheory.BusyBeaver.ZFC.RegisterPartial

theorem run_eq (p : RegisterPath.Program) (n : Nat) (c : RegisterPath.Configuration) :
    TerminalDrain.run (RegisterPath.step p) n c = RegisterPath.run p n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [TerminalDrain.run, RegisterPath.run]
      cases RegisterPath.step p c with
      | none => rfl
      | some d => exact ih d

theorem halts_iff {p : RegisterPath.Program}
    (hstop : ∀ {c}, RegisterPath.step p c = none → RegisterPath.AtHalt p c)
    (c : RegisterPath.Configuration) :
    TerminalDrain.Halts (RegisterPath.step p) c ↔ RegisterPath.Halts p c := by
  constructor
  · rintro ⟨n, d, hn, hd⟩
    exact ⟨n, d, (run_eq p n c) ▸ hn, hstop hd⟩
  · rintro ⟨n, d, hn, k, hk⟩
    refine ⟨n, d, (run_eq p n c).symm ▸ hn, ?_⟩
    simp [RegisterPath.step, hk, RegisterPath.execute]

end SetTheory.BusyBeaver.ZFC.RegisterPartial
