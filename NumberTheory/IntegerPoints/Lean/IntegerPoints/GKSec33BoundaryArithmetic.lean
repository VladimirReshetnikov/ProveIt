import IntegerPoints.GKSec33ParameterChoice

/-!
# Graham--Kolesnik section 3.3: square-root boundary arithmetic

This module isolates the scale calculations at the end of the square-root
boundary argument.  If `H = Q^2` and `delta = 1 - 2k`, the choice
`16 A <= Q^delta` makes the exponent-pair contribution at most one sixteenth
of the resonant main term.  The analogous quadratic choice controls the
`B`-process error, and a final Archimedean choice absorbs the fixed terms.

Keeping these facts separate makes the analytic proof independent of the
particular normal forms chosen for powers and divisions by later modules.
-/

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- The exponent-pair term is a sixteenth of the resonant scale after the
choice `16 A <= Q^(1 - 2k)`. -/
theorem exponent_term_le_sixteenth {A k δ Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 ≤ R)
    (hδ : δ = 1 - 2 * k) (hAQ : 16 * A ≤ Q ^ δ) :
    A * (R * (Q ^ 2) ^ k) ≤ R * Q / 16 := by
  have hA_le : A ≤ Q ^ δ / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    simpa only [mul_comm] using hAQ
  have hpow : (Q ^ 2) ^ k = Q ^ (2 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    ring_nf
  have hcombine : Q ^ δ * (Q ^ 2) ^ k = Q := by
    rw [hpow, ← Real.rpow_add hQ, hδ]
    have hexp : 1 - 2 * k + 2 * k = (1 : ℝ) := by ring
    rw [hexp, Real.rpow_one]
  calc
    A * (R * (Q ^ 2) ^ k) = R * (A * (Q ^ 2) ^ k) := by ring
    _ ≤ R * ((Q ^ δ / 16) * (Q ^ 2) ^ k) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg (sq_nonneg Q) k)) hR
    _ = R * Q / 16 := by
      rw [div_mul_eq_mul_div, hcombine]
      ring

/-- The scale-dependent error from the `B`-process is a sixteenth of the
resonant scale after the choice `16 B <= Q^2`. -/
theorem bprocess_term_le_sixteenth {B Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 ≤ R)
    (hBQ : 16 * B ≤ Q ^ 2) :
    B * (R / Q) ≤ R * Q / 16 := by
  have hB_le : B ≤ Q ^ 2 / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    simpa only [mul_comm] using hBQ
  calc
    B * (R / Q) ≤ (Q ^ 2 / 16) * (R / Q) := by
      exact mul_le_mul_of_nonneg_right hB_le (div_nonneg hR hQ.le)
    _ = R * Q / 16 := by field_simp [hQ.ne']

/-- A fixed nonnegative remainder bounded by `M/16` is also bounded by one
sixteenth of `R Q` whenever `M <= R` and `Q >= 1`. -/
theorem fixed_term_le_sixteenth {K M R Q : ℝ}
    (hK : K ≤ M / 16) (hM : 0 ≤ M) (hMR : M ≤ R) (hQ : 1 ≤ Q) :
    K ≤ R * Q / 16 := by
  have hMQ : M ≤ R * Q := by nlinarith
  exact hK.trans ((div_le_div_iff_of_pos_right
    (by norm_num : (0 : ℝ) < 16)).2 hMQ)

/-- Three one-sixteenth contributions are strictly smaller than a
one-quarter main term at every positive scale. -/
theorem three_sixteenths_lt_quarter {X U : ℝ}
    (hX : 0 < X) (hU : U ≤ 3 * X / 16) :
    U < X / 4 := by
  linarith

end GKSec33

end LeanProofs.IntegerPoints
