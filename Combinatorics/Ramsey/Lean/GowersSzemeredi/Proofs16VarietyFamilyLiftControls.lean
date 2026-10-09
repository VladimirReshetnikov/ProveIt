import GowersSzemeredi.Proofs16VarietyUniformLiftControls

/-! Uniform interpolation controls when each sampled slice has `Q`
variety pieces. The candidate count is quartic in the sample ceiling
and quadratic in the number of pieces per slice.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_variety_family_candidate_count_le_quartic {Q : Nat}
    (hQ : 0 < Q) (r : Nat) :
    section16CompressedCandidateCount r (9 * (r * Q)) ≤ 81 * (max 1 r)^4 * Q^2 := by
  have hcount : 9 * (r * Q) ≤ 3 * (max 1 r * (3 * Q)) := by
    calc
      _ ≤ 9 * (max 1 r * Q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right Q (le_max_right _ _))
      _ = 3 * (max 1 r * (3 * Q)) := by ring
  have hmono : section16CompressedCandidateCount r (9 * (r * Q)) ≤
      section16CompressedCandidateCount r (3 * (max 1 r * (3 * Q))) := by
    unfold section16CompressedCandidateCount
    exact max_le_max hcount (Nat.mul_le_mul (Nat.mul_le_mul_left _ hcount) hcount)
  calc
    _ ≤ section16CompressedCandidateCount r (3 * (max 1 r * (3 * Q))) := hmono
    _ ≤ 9 * (max 1 r)^4 * (3 * Q)^2 :=
      section16_cubic_candidate_count_le_quartic (Nat.mul_pos (by decide) hQ)
    _ = 81 * (max 1 r)^4 * Q^2 := by ring

theorem section16_variety_family_uniform_lift_controls (C D : Nat) {p Q qGamma k : Nat}
    (hp : 0 < p) (hQ : 0 < Q) {c sigma theta gamma : Real}
    (hc : 0 < c) (hc1 : c ≤ 1) (hs : 0 < sigma)
    (hcount : (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
    let R := section16UniformSampleCount sigma theta gamma k
    section16PolynomialJointVarietyExponent C p (R * Q) D c ≤
      section16PolynomialJointVarietyExponent C p (r * Q) D c ∧
      max (9 * (r * Q : Nat) : Real)
        ((r.choose 2 : Real) * (9 * (r * Q : Nat)) * (9 * (r * Q : Nat))) ≤
        81 * (R : Real)^4 * (Q : Real)^2 := by
  intro r R
  have hrR : r ≤ R := section16_sample_count_le_uniform hs hcount
  have hR : 0 < R := section16UniformSampleCount_pos k hs
  refine ⟨section16PolynomialJointVarietyExponent_antitone_count C D hp
    (Nat.mul_le_mul_right Q hrR) hc hc1, ?_⟩
  have hbudget := section16_variety_family_candidate_count_le_quartic hQ r
  have hpad : max 1 r ≤ R := max_le hR hrR
  have h := hbudget.trans (Nat.mul_le_mul_right (Q^2)
    (Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left hpad 4)))
  unfold section16CompressedCandidateCount at h
  exact_mod_cast h

end LeanProofs.GowersSzemeredi
