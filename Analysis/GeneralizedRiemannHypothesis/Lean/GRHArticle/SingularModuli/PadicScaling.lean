import GRHArticle.SingularModuli.PadicConvergence

/-!
# Scaling at rational p-adic depth

The p-adic complex field contains a scaling element of any specified rational
depth. This lets the sparse-polynomial disk argument choose its radius factor.
-/

namespace GRHArticle.SingularModuli

/-- A rational depth is realized by the norm of a p-adic complex number. -/
theorem exists_norm_eq_rpow_neg_depth {p : ℕ} [hp : Fact (Nat.Prime p)] (r : ℚ) :
    ∃ b : ℂ_[p], ‖b‖ = (p : ℝ) ^ (-(r : ℝ)) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ r.num) r.den_pos
  have hp_norm : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [padicComplex_norm_natCast p hp.out.ne_zero, padicValNat_self, Nat.cast_one,
      zpow_neg, zpow_one]
  have hnorm : ‖b‖ ^ r.den = (p : ℝ) ^ (-r.num) := by
    rw [← norm_pow, hb, norm_zpow, hp_norm, inv_zpow, zpow_neg]
  have hden : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_pos.ne'
  have hr : -(r : ℝ) * (r.den : ℝ) = ((-r.num : ℤ) : ℝ) := by
    rw [Rat.cast_def, neg_mul, div_mul_cancel₀ _ hden, Int.cast_neg]
  have htarget : ((p : ℝ) ^ (-(r : ℝ))) ^ r.den = (p : ℝ) ^ (-r.num) := by
    rw [← Real.rpow_mul_natCast hp₀.le, hr, Real.rpow_intCast]
  exact ⟨b, (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp₀.le _) r.den_pos.ne').mp
    (hnorm.trans htarget.symm)⟩

end GRHArticle.SingularModuli
