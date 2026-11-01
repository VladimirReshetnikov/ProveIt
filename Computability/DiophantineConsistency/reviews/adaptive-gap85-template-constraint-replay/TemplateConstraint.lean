import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Order.Basic

/-! A necessary congruence for a specific artificial-port Pell template.
It does not assert existence or nonexistence of an 85-zero. -/
theorem template_divisibility (X Y q T U gamma S : ℤ)
    (hU : Y ∣ U)
    (hroot :
      U * S = U * (X + (Y * (X + 1)) * (4 * ((Y * (X + 1))^2 +
        4 * (Y * (X + 1)) + 3) + 3)) +
        (4 * (Y * (X + 1)) + 3) * (U * gamma + X * Y * q -
          (8 * X * Y^2 + 4) +
          ((4 * ((Y * (X + 1))^2 + 4 * (Y * (X + 1)) + 3) + 3) * T -
            4 * ((Y * (X + 1))^2 + 4 * (Y * (X + 1)) + 3)) + 1)) :
    Y ∣ 45 * (T - 1) := by
  let a := Y * (X + 1)
  let D := a^2 + 4*a + 3
  let H := 4*a + 3
  let c := 4*D + 3
  let B := X*Y*q - (8*X*Y^2+4) + (c*T-4*D) + 1
  have hr : U*S = U*(X+a*c) + H*(U*gamma+B) := by
    dsimp [a,D,H,c,B]
    ring_nf at hroot ⊢
    exact hroot
  obtain ⟨u, hu⟩ := hU
  have hdiv : Y ∣ H*B := by
    refine ⟨u*S - u*(X+a*c) - H*u*gamma, ?_⟩
    calc
      H*B = U*S - U*(X+a*c) - H*(U*gamma) := by rw [hr]; ring
      _ = Y*(u*S - u*(X+a*c) - H*u*gamma) := by rw [hu]; ring
  have hid : H*B = 45*(T-1) + Y*(H*X*(q-8*Y) +
      (X+1)*(16*a^2+76*a+108)*(T-1)) := by dsimp [a,D,H,c,B]; ring
  rw [hid] at hdiv
  obtain ⟨v, hv⟩ := hdiv
  refine ⟨v - (H*X*(q-8*Y) + (X+1)*(16*a^2+76*a+108)*(T-1)), ?_⟩
  calc
    45*(T-1) = Y*v - Y*(H*X*(q-8*Y) + (X+1)*(16*a^2+76*a+108)*(T-1)) := by
      rw [←hv]
      ring
    _ = Y*(v - (H*X*(q-8*Y) + (X+1)*(16*a^2+76*a+108)*(T-1))) := by ring

/-- For the same restricted template, a small positive T must equal one. -/
theorem template_small_T (Y T : ℤ) (hT : 1 ≤ T)
    (hsmall : 45 * (T - 1) < Y) (hdiv : Y ∣ 45 * (T - 1)) : T = 1 := by
  have hn : 0 ≤ 45 * (T - 1) := Int.mul_nonneg_of_nonneg_or_nonpos (Or.inl ⟨by decide, sub_nonneg.mpr hT⟩)
  have hz : 45 * (T - 1) = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hn hsmall hdiv
  have he : T - 1 = 0 := (mul_eq_zero.mp hz).resolve_left (by decide)
  exact sub_eq_zero.mp he
