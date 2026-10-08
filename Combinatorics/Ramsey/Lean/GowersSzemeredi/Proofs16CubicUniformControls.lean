import GowersSzemeredi.Proofs16CubicCoverControls
import GowersSzemeredi.Proofs16UniformLiftControls

/-! Uniform controls for the cubic sampled-slice provider.
Replace the graph count selected by the line-cover proof by its uniform
sample ceiling. The cubic exponent decreases and the interpolation budget
increases in the required directions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Increasing a positive graph count decreases the cubic exponent. -/
theorem cubicBaseExponent_antitone_count {q Q : Nat} {sigma : Real}
    (hq : 0 < q) (hqQ : q ≤ Q) (hs : 0 ≤ sigma) :
    cubicBaseExponent Q sigma ≤ cubicBaseExponent q sigma := by
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  unfold cubicBaseExponent
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.pow_le_pow_left hqQ 4

/-- The concrete slice count gives a quartic bound on the number of
interpolated graphs, including the empty-sample fallback. -/
theorem section16_cubic_candidate_count_le_quartic {r q : Nat} (hq : 0 < q) :
    section16CompressedCandidateCount r (3 * (max 1 r * q)) ≤
      9 * (max 1 r) ^ 4 * q ^ 2 := by
  have hR : max 1 r ≤ (max 1 r) ^ 4 :=
    le_self_pow₀ (le_max_left _ _) (by decide)
  have hq2 : q ≤ q ^ 2 := le_self_pow₀ (by omega) (by decide)
  have hc : r.choose 2 ≤ (max 1 r) ^ 2 :=
    (Nat.choose_le_pow r 2).trans (Nat.pow_le_pow_left (le_max_right _ _) 2)
  unfold section16CompressedCandidateCount
  apply max_le
  · calc
      3 * (max 1 r * q) ≤ 9 * ((max 1 r) ^ 4 * q ^ 2) :=
        Nat.mul_le_mul (by decide) (Nat.mul_le_mul hR hq2)
      _ = 9 * (max 1 r) ^ 4 * q ^ 2 := by ring
  · calc
      r.choose 2 * (3 * (max 1 r * q)) * (3 * (max 1 r * q))
          ≤ (max 1 r) ^ 2 * (3 * (max 1 r * q)) * (3 * (max 1 r * q)) := by gcongr
      _ = 9 * (max 1 r) ^ 4 * q ^ 2 := by ring

/-- A uniform sample ceiling controls both the slice exponent and the
complete compressed interpolation budget. -/
theorem section16_cubic_uniform_lift_controls {q qGamma k : Nat}
    {sigma theta gamma : Real} (hq : 0 < q) (hs : 0 < sigma)
    (hcount : (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
    let R := section16UniformSampleCount sigma theta gamma k
    let p : Real := ((3 * (max 1 r * q) : Nat) : Real)
    let pUniform : Real := ((3 * (R * q) : Nat) : Real)
    cubicBaseExponent (R * q) sigma ≤ cubicBaseExponent (max 1 r * q) sigma ∧
      max p ((r.choose 2 : Real) * p * p) ≤
        max pUniform ((R.choose 2 : Real) * pUniform * pUniform) := by
  intro r R p pUniform
  have hr : 0 < r := Nat.ceil_pos.mpr
    (div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))) hs)
  have hrR : r ≤ R := section16_sample_count_le_uniform hs hcount
  have hpad : max 1 r = r := max_eq_right hr
  have hp : max 1 r * q ≤ R * q := by rw [hpad]; exact Nat.mul_le_mul_right q hrR
  refine ⟨cubicBaseExponent_antitone_count (Nat.mul_pos (by omega) hq) hp hs.le, ?_⟩
  apply section16_compressed_budget_mono hrR (by positivity)
  change ((3 * (max 1 r * q) : Nat) : Real) ≤ ((3 * (R * q) : Nat) : Real)
  exact_mod_cast Nat.mul_le_mul_left 3 hp

end LeanProofs.GowersSzemeredi
