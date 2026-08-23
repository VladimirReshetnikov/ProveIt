import IntegerPoints.GKSec33SqrtPhase

/-!
# Graham--Kolesnik section 3.3: the square-root exponent-pair bound

We specialize an exponent-pair estimate with second coordinate `1 / 2` to
the phase `x \mapsto 2 t \sqrt{x}` and the parameters
`H = Q^2`, `N = R^2`, and `t = H R`.  With these square parameters, both
real powers of `N` simplify exactly and the estimate becomes
`A (R H^k + H⁻¹)`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- On a positive integral dyadic interval, the smooth extension used for
class membership gives exactly the original square-root exponential sum. -/
theorem sqrtPhase_sum_eq_sqrt_sum (N : ℕ) (t : ℝ) (hN : 0 < N) :
    ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (sqrtPhase t n) =
      ∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
        e (2 * t * Real.sqrt n) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := hn
  unfold intRange at hn'
  simp only [Finset.mem_Ioc, Nat.floor_natCast] at hn'
  have hnpos : 0 < n := hN.trans hn'.1
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hnhalf : (1 / 2 : ℝ) ≤ (n : ℝ) := by linarith
  simp only [sqrtPhase, L9.hfun_eq hnhalf]

/-- If `(k, 1 / 2)` is an exponent pair, its estimate on the square-root
phase has a single nonnegative constant and the exact specialized shape
`A (R H^k + H⁻¹)` for `H = Q²`, `N = R²`, and `t = HR`. -/
theorem exists_sqrt_exponent_bound {k : ℝ}
    (hpair : IsExponentPair k (1 / 2)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q R : ℕ), 0 < Q → 0 < R →
      let H : ℕ := Q ^ 2
      let N : ℕ := R ^ 2
      let t : ℝ := (H : ℝ) * (R : ℝ)
      ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
          e (2 * t * Real.sqrt n)‖ ≤
        A * ((R : ℝ) * (H : ℝ) ^ k + (H : ℝ)⁻¹) := by
  obtain ⟨P, ε, C, hε, _hεhalf, hbound⟩ :=
    hpair.2.2.2.2 (1 / 2) (by norm_num)
  let A : ℝ := max C 0
  have hA : 0 ≤ A := by simp only [A, le_max_right]
  refine ⟨A, hA, ?_⟩
  intro Q R hQ hR
  dsimp only
  let H : ℕ := Q ^ 2
  let N : ℕ := R ^ 2
  let t : ℝ := (H : ℝ) * (R : ℝ)
  change
    ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
        e (2 * t * Real.sqrt n)‖ ≤
      A * ((R : ℝ) * (H : ℝ) ^ k + (H : ℝ)⁻¹)
  have hH : 0 < H := by
    exact pow_pos hQ 2
  have hN : 0 < N := by
    exact pow_pos hR 2
  have hHR : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.2 hH
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 hN
  have hRR : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.2 hR
  have ht : 0 < t := by
    exact mul_pos hHR hRR
  have hNhalf : (1 / 2 : ℝ) < (N : ℝ) := by
    have hNgeOne : 1 ≤ N := by omega
    have hNgeOneReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNgeOne
    linarith
  have hclass :
      InGKClass (N : ℝ) P (1 / 2) t ε
        (N : ℝ) (2 * (N : ℝ)) (sqrtPhase t) :=
    sqrtPhase_mem_gkClass P hNhalf hε ht
  have hraw := hbound (N : ℝ) t (N : ℝ) (2 * (N : ℝ))
    (sqrtPhase t) hNR ht hclass
  rw [sqrtPhase_sum_eq_sqrt_sum N t hN] at hraw
  have hNcast : (N : ℝ) = (R : ℝ) ^ 2 := by
    simp only [N, Nat.cast_pow]
  have hroot : (N : ℝ) ^ (1 / 2 : ℝ) = (R : ℝ) := by
    rw [← Real.sqrt_eq_rpow, hNcast, Real.sqrt_sq_eq_abs,
      abs_of_pos hRR]
  have hinvRoot : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (R : ℝ)⁻¹ := by
    rw [Real.rpow_neg hNR.le, hroot]
  have hscale :
      t * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (H : ℝ) := by
    rw [hinvRoot]
    simp only [t, mul_assoc, mul_inv_cancel₀ hRR.ne', mul_one]
  have herr :
      t⁻¹ * (N : ℝ) ^ (1 / 2 : ℝ) = (H : ℝ)⁻¹ := by
    rw [hroot]
    simp only [t, mul_inv, mul_assoc, inv_mul_cancel₀ hRR.ne', mul_one]
  have hraw' := hraw
  rw [hscale, herr, hroot] at hraw'
  have hinside :
      0 ≤ (R : ℝ) * (H : ℝ) ^ k + (H : ℝ)⁻¹ := by
    positivity
  calc
    ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)),
        e (2 * t * Real.sqrt n)‖ ≤
        C * ((R : ℝ) * (H : ℝ) ^ k + (H : ℝ)⁻¹) := by
      simpa only [mul_comm] using hraw'
    _ ≤ A * ((R : ℝ) * (H : ℝ) ^ k + (H : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hinside

end GKSec33

end LeanProofs.IntegerPoints
