import IntegerPoints.GKStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Graham--Kolesnik section 3.3: finite parameter choices

Small Archimedean lemmas used to choose the integer parameters in the
boundary-case argument.  The first result is stated slightly more generally
than needed: the lower bounds on `A` and `B` play no role in the existence of
a sufficiently large natural number.
-/

open Filter

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- Given a positive real exponent, one natural parameter can simultaneously
dominate a fixed lower bound, a real-power threshold, and a quadratic
threshold. -/
theorem exists_nat_parameter_choice (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, 4 ≤ Q ∧ 16 * A ≤ (Q : ℝ) ^ δ ∧
      16 * B ≤ (Q : ℝ) ^ 2 := by
  have hrpow :
      Tendsto (fun Q : ℕ => (Q : ℝ) ^ δ) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop hδ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsq :
      Tendsto (fun Q : ℕ => (Q : ℝ) ^ 2) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_pow_atTop (α := ℝ) (show (2 : ℕ) ≠ 0 by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hA : ∀ᶠ Q : ℕ in atTop, 16 * A ≤ (Q : ℝ) ^ δ :=
    hrpow.eventually (eventually_ge_atTop (16 * A))
  have hB : ∀ᶠ Q : ℕ in atTop, 16 * B ≤ (Q : ℝ) ^ 2 :=
    hsq.eventually (eventually_ge_atTop (16 * B))
  obtain ⟨Q, hQ, hQA, hQB⟩ :=
    ((eventually_ge_atTop (4 : ℕ)).and (hA.and hB)).exists
  exact ⟨Q, hQ, hQA, hQB⟩

/-- A nonnegative real scale is at most one sixteenth of some positive
natural number. -/
theorem exists_pos_nat_scale {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℕ, 0 < M ∧ K ≤ (M : ℝ) / 16 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * K)
  have hMposReal : (0 : ℝ) < (M : ℝ) :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) hK) hM
  refine ⟨M, Nat.cast_pos.mp hMposReal, ?_⟩
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
  simpa only [mul_comm] using hM.le

end GKSec33

end LeanProofs.IntegerPoints
