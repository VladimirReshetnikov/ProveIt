import DavisEntringerGrahamSimmons1977.CountingRecurrences
import RamseyPaperCommon.ThreeFreeCounting
import Sharma2012.Statements

set_option autoImplicit false

namespace LeanProofs.Sharma2012

private theorem theta_eq_davis_M (n : Nat) :
    theta n = LeanProofs.DavisEntringerGrahamSimmons1977.M n := by
  rw [LeanProofs.RamseyPaperCommon.sharma_theta_eq_M,
    ← LeanProofs.RamseyPaperCommon.davis_M_eq_lesaulnier_M]

theorem theorem_1_1_holds : theorem_1_1 := by
  intro n hn
  rw [theta_eq_davis_M]
  exact LeanProofs.DavisEntringerGrahamSimmons1977.fact_1_holds n hn

theorem inequality_1_holds : inequality_1 := by
  intro k hk
  simp only [theta_eq_davis_M]
  exact LeanProofs.DavisEntringerGrahamSimmons1977.even_count_recurrence_holds k hk

theorem inequality_2_holds : inequality_2 := by
  intro k hk
  simp only [theta_eq_davis_M]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    LeanProofs.DavisEntringerGrahamSimmons1977.odd_count_recurrence_holds k hk

end LeanProofs.Sharma2012

