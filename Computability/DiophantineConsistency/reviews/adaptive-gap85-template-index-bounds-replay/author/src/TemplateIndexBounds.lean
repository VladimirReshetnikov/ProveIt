import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Order.Basic

/-! Algebraic bounds for one 85-gap Pell template. A Pell-index trichotomy is
explicit; it is not proved from an arbitrary zero in this file. -/

theorem template_index_bounds (X Y : ℤ) (hX : 1 ≤ X) (hY : 8 ≤ Y) :
    let a := Y*(X+1)
    let s := X*Y^2
    let c := 4*(a^2+4*a+3)+3
    2*(Y+1) < c ∧ c < Y*(32*s^2-32*s+6) := by
  let a := Y*(X+1)
  let s := X*Y^2
  have hY0 : 0 ≤ Y := by omega
  have hs : 64 ≤ s := by
    dsimp [s]
    nlinarith [sq_nonneg Y, mul_nonneg (show 0 ≤ X-1 by omega) (sq_nonneg Y)]
  have ha : 0 ≤ a := by dsimp [a]; nlinarith
  have hay : a ≤ s := by
    have hx : X+1 ≤ X*Y := by nlinarith [mul_nonneg (show 0 ≤ X-1 by omega) (show 0 ≤ Y-2 by omega)]
    have hp := mul_nonneg (show 0 ≤ X*Y-(X+1) by nlinarith) hY0
    dsimp [a,s]
    nlinarith
  have hasq : a^2 ≤ s^2 := by nlinarith [sq_nonneg (s-a)]
  have hs64 : 0 ≤ s*(s-64) := mul_nonneg (by omega) (by omega)
  have hc : 4*(a^2+4*a+3)+3 < 32*s^2-32*s+6 := by nlinarith
  have hpos : 0 < 32*s^2-32*s+6 := by nlinarith
  have hmul : 0 ≤ (Y-1)*(32*s^2-32*s+6) := mul_nonneg (by omega) (by omega)
  dsimp only
  constructor
  · nlinarith [sq_nonneg (a-1)]
  · nlinarith

/-- If the positive first-norm Pell index has the stated first/second/third
trichotomy, positivity forces the second index in this special template. -/
theorem second_template_index (X Y eta zeta k : ℤ)
    (hX : 1 ≤ X) (hY : 8 ≤ Y) (he : 0 < eta) (hz : 0 < zeta)
    (hk : k=eta+zeta)
    (hc : eta+Y*k = 4*((Y*(X+1))^2+4*(Y*(X+1))+3)+3)
    (hcases : k=2 ∨ k=8*(X*Y^2)+4 ∨ 32*(X*Y^2)^2-32*(X*Y^2)+6 ≤ k) :
    k=8*(X*Y^2)+4 := by
  have h := template_index_bounds X Y hX hY
  dsimp only at h
  rcases hcases with h1 | h2 | h3
  · subst k
    nlinarith
  · exact h2
  · have hmul : 0 ≤ Y*(k-(32*(X*Y^2)^2-32*(X*Y^2)+6)) := mul_nonneg (by omega) (by omega)
    nlinarith
