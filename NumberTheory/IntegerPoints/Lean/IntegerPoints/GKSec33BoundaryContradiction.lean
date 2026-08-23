import IntegerPoints.GKSec33BoundaryArithmetic

/-!
# Graham--Kolesnik section 3.3: the square-root boundary contradiction

This module packages the final diagonal parameter choice in the proof that an
exponent pair `(k, 1 / 2)` has `k = 1 / 2`.  It is deliberately independent
of the analytic definitions of the original and dual sums.  Later modules
only need to supply their exponent-pair upper bound, `B`-process error, and
factorial-resonance lower bound in the displayed normal forms.
-/

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- The abstract square-root boundary argument.  Bounds of the exact forms
produced by the exponent-pair estimate and Lemma 3.6, together with the
factorial resonant lower bound for the dual sum, force `k = 1 / 2`.

The functions `S Q R` and `D Q R` stand respectively for the original and
dual exponential sums at `H = Q^2`, `N = R^2`, and `t = HR`. -/
theorem k_eq_half_of_sqrt_bounds {k A B : ℝ} (S D : ℕ → ℕ → ℂ)
    (hk : k ≤ 1 / 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hupper : ∀ (Q R : ℕ), 0 < Q → 0 < R →
      ‖S Q R‖ ≤ A * ((R : ℝ) * ((Q : ℝ) ^ 2) ^ k + ((Q : ℝ) ^ 2)⁻¹))
    (herror : ∀ (Q R : ℕ), 0 < Q → 0 < R →
      ‖S Q R - D Q R‖ ≤
        B * (Real.log ((Q : ℝ) ^ 2 + 2) + (R : ℝ) / (Q : ℝ)))
    (hlower : ∀ (Q M : ℕ), 0 < Q → 0 < M →
      let H : ℕ := Q ^ 2
      let R : ℕ := M * H.factorial
      (R : ℝ) * (Q : ℝ) / 4 ≤ ‖D Q R‖) :
    k = 1 / 2 := by
  apply le_antisymm hk
  by_contra hnot
  have hklt : k < 1 / 2 := lt_of_not_ge hnot
  let δ : ℝ := 1 - 2 * k
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  obtain ⟨Q, hQ4, hAQ, hBQ⟩ := exists_nat_parameter_choice A B hδ
  have hQ : 0 < Q := by omega
  have hQreal : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.2 hQ
  let H : ℕ := Q ^ 2
  let K : ℝ := A * ((Q : ℝ) ^ 2)⁻¹ +
    B * Real.log ((Q : ℝ) ^ 2 + 2)
  have hlog : 0 ≤ Real.log ((Q : ℝ) ^ 2 + 2) := by
    apply Real.log_nonneg
    nlinarith [sq_nonneg (Q : ℝ)]
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg (mul_nonneg hA (inv_nonneg.mpr (sq_nonneg _)))
      (mul_nonneg hB hlog)
  obtain ⟨M, hM, hKM⟩ := exists_pos_nat_scale hK
  let R : ℕ := M * H.factorial
  have hR : 0 < R := by
    exact mul_pos hM (Nat.factorial_pos H)
  have hRreal : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.2 hR
  have hMRnat : M ≤ R := by
    dsimp only [R]
    nlinarith [Nat.factorial_pos H]
  have hMR : (M : ℝ) ≤ (R : ℝ) := by exact_mod_cast hMRnat
  have hExp :
      A * ((R : ℝ) * ((Q : ℝ) ^ 2) ^ k) ≤
        (R : ℝ) * (Q : ℝ) / 16 := by
    exact exponent_term_le_sixteenth hQreal hRreal.le rfl hAQ
  have hBproc :
      B * ((R : ℝ) / (Q : ℝ)) ≤
        (R : ℝ) * (Q : ℝ) / 16 := by
    exact bprocess_term_le_sixteenth hQreal hRreal.le hBQ
  have hFixed : K ≤ (R : ℝ) * (Q : ℝ) / 16 := by
    exact fixed_term_le_sixteenth hKM (Nat.cast_nonneg M) hMR
      (by exact_mod_cast (show 1 ≤ Q by omega))
  have hS :
      ‖S Q R‖ ≤ (R : ℝ) * (Q : ℝ) / 16 +
        A * ((Q : ℝ) ^ 2)⁻¹ := by
    calc
      ‖S Q R‖ ≤
          A * ((R : ℝ) * ((Q : ℝ) ^ 2) ^ k + ((Q : ℝ) ^ 2)⁻¹) :=
        hupper Q R hQ hR
      _ = A * ((R : ℝ) * ((Q : ℝ) ^ 2) ^ k) +
          A * ((Q : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ (R : ℝ) * (Q : ℝ) / 16 + A * ((Q : ℝ) ^ 2)⁻¹ :=
        add_le_add hExp le_rfl
  have hE :
      ‖S Q R - D Q R‖ ≤
        B * Real.log ((Q : ℝ) ^ 2 + 2) +
          (R : ℝ) * (Q : ℝ) / 16 := by
    calc
      ‖S Q R - D Q R‖ ≤
          B * (Real.log ((Q : ℝ) ^ 2 + 2) +
            (R : ℝ) / (Q : ℝ)) := herror Q R hQ hR
      _ = B * Real.log ((Q : ℝ) ^ 2 + 2) +
          B * ((R : ℝ) / (Q : ℝ)) := by ring
      _ ≤ B * Real.log ((Q : ℝ) ^ 2 + 2) +
          (R : ℝ) * (Q : ℝ) / 16 := add_le_add le_rfl hBproc
  have hD : ‖D Q R‖ ≤ 3 * ((R : ℝ) * (Q : ℝ)) / 16 := by
    calc
      ‖D Q R‖ = ‖S Q R - (S Q R - D Q R)‖ := by ring_nf
      _ ≤ ‖S Q R‖ + ‖S Q R - D Q R‖ := norm_sub_le _ _
      _ ≤ ((R : ℝ) * (Q : ℝ) / 16 + A * ((Q : ℝ) ^ 2)⁻¹) +
          (B * Real.log ((Q : ℝ) ^ 2 + 2) +
            (R : ℝ) * (Q : ℝ) / 16) := add_le_add hS hE
      _ = 2 * ((R : ℝ) * (Q : ℝ)) / 16 + K := by
        dsimp only [K]
        ring
      _ ≤ 3 * ((R : ℝ) * (Q : ℝ)) / 16 := by linarith
  have hDlow : (R : ℝ) * (Q : ℝ) / 4 ≤ ‖D Q R‖ := by
    simpa only [H, R] using hlower Q M hQ hM
  have hDstrict : ‖D Q R‖ < (R : ℝ) * (Q : ℝ) / 4 := by
    apply three_sixteenths_lt_quarter (mul_pos hRreal hQreal)
    simpa only [mul_assoc] using hD
  exact (not_lt_of_ge hDlow) hDstrict

end GKSec33

end LeanProofs.IntegerPoints
