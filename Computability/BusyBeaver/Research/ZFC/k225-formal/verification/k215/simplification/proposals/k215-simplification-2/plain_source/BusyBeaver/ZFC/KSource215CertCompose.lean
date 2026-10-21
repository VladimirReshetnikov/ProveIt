import BusyBeaver.ZFC.KSource215CertParts

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim

/-- Combine checked halves without reducing any certificate entries again. -/
theorem allC_of_halves (f : Entry → Bool) (T : CTree)
    (hl : allC f (certLeft T) = true)
    (hr : allC f (certRight T) = true) : allC f T = true := by
  cases T with
  | empty => rfl
  | leaf x => exact hl
  | branch cut l r =>
      change allC f l = true at hl
      change allC f r = true at hr
      rw [allC, hl, hr]
      rfl

end SetTheory.BusyBeaver.ZFC.KSource215
