import BusyBeaver.ZFC.KZip
import BusyBeaver.ZFC.TerminalDrain

/-! The existing zipper definitions are retained. These equalities provide
the adapter to the generic deterministic partial-transition theorem. -/

namespace SetTheory.BusyBeaver.ZFC.KPartial

theorem run_eq (M : KZip.TMN) (n : Nat) (c : KZip.Conf) :
    TerminalDrain.run (KZip.step M) n c = KZip.run M n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simp only [TerminalDrain.run, KZip.run]
      cases KZip.step M c with
      | none => rfl
      | some d => exact ih d

theorem halts_iff (M : KZip.TMN) (c : KZip.Conf) :
    TerminalDrain.Halts (KZip.step M) c ↔ KZip.Halts M c := by
  constructor
  · rintro ⟨n, d, hn, hd⟩
    exact ⟨d, ⟨n, (run_eq M n c) ▸ hn⟩, hd⟩
  · rintro ⟨d, ⟨n, hn⟩, hd⟩
    exact ⟨n, d, (run_eq M n c).symm ▸ hn, hd⟩

theorem halts_of_reach {M : KZip.TMN} {a b : KZip.Conf}
    (h : KZip.Reach M a b) (ha : KZip.Halts M a) : KZip.Halts M b := by
  obtain ⟨n, hn⟩ := h
  exact (halts_iff M b).mp ((TerminalDrain.halts_iff_of_run
    ((run_eq M n a).symm ▸ hn)).mp ((halts_iff M a).mpr ha))

end SetTheory.BusyBeaver.ZFC.KPartial
