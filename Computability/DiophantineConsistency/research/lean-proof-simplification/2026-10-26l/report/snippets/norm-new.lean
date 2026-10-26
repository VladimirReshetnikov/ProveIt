theorem norm_ne_zero_of_not_isSquare (d x y : ℤ) (hd : ¬ IsSquare d) (hy : y ≠ 0) :
    x ^ 2 - d * y ^ 2 ≠ 0 := by
  intro h
  have he : x ^ 2 = y ^ 2 * d := by nlinarith only [h]
  obtain ⟨k, hk⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp
    (show y ^ 2 ∣ x ^ 2 from ⟨d, he⟩)
  exact hd ⟨k, by
    rw [hk, mul_pow] at he
    simpa only [pow_two] using (mul_left_cancel₀ (pow_ne_zero 2 hy) he).symm⟩
