import GowersSzemeredi.Proofs16JointVarietyCapBound
import GowersSzemeredi.Proofs16CubicUniformControls

/-! Uniform interpolation controls for the variety-piece slice provider.
The cover exponent decreases with the sample count; the interpolation
budget has a quartic bound independent of the input box.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16PolynomialJointVarietyExponent_antitone_count (C D : Nat)
    {p n m : Nat} (hp : 0 < p) (hnm : n ≤ m) {c : Real}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    section16PolynomialJointVarietyExponent C p m D c ≤
      section16PolynomialJointVarietyExponent C p n D c := by
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
  unfold section16PolynomialJointVarietyExponent
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr

/-- The nine graphs per sampled slice yield a quartic candidate budget. -/
theorem section16_variety_candidate_count_le_quartic (r : Nat) :
    section16CompressedCandidateCount r (9 * r) ≤ 81 * (max 1 r)^4 := by
  have hcount : 9 * r ≤ 3 * (max 1 r * 3) := by
    have h := le_max_right 1 r
    omega
  have hmono : section16CompressedCandidateCount r (9 * r) ≤
      section16CompressedCandidateCount r (3 * (max 1 r * 3)) := by
    unfold section16CompressedCandidateCount
    exact max_le_max hcount (Nat.mul_le_mul (Nat.mul_le_mul_left _ hcount) hcount)
  have h := section16_cubic_candidate_count_le_quartic (r := r) (q := 3) (by decide)
  calc
    _ ≤ section16CompressedCandidateCount r (3 * (max 1 r * 3)) := hmono
    _ ≤ 9 * (max 1 r)^4 * 3^2 := h
    _ = 81 * (max 1 r)^4 := by ring

/-- A uniform sample ceiling supplies both the exponent and the quartic
candidate budget for the general affine lift. -/
theorem section16_variety_uniform_lift_controls (C D : Nat) {p qGamma k : Nat}
    (hp : 0 < p) {c sigma theta gamma : Real} (hc : 0 < c) (hc1 : c ≤ 1)
    (hs : 0 < sigma)
    (hcount : (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
    let R := section16UniformSampleCount sigma theta gamma k
    section16PolynomialJointVarietyExponent C p R D c ≤
      section16PolynomialJointVarietyExponent C p r D c ∧
      max (9 * r : Real) ((r.choose 2 : Real) * (9 * r) * (9 * r)) ≤
        81 * (R : Real)^4 := by
  intro r R
  have hrR : r ≤ R := section16_sample_count_le_uniform hs hcount
  have hR : 0 < R := section16UniformSampleCount_pos k hs
  refine ⟨section16PolynomialJointVarietyExponent_antitone_count C D hp hrR hc hc1, ?_⟩
  have hbudget := section16_variety_candidate_count_le_quartic r
  have hpad : max 1 r ≤ R := max_le hR hrR
  have h := hbudget.trans (Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left hpad 4))
  unfold section16CompressedCandidateCount at h
  exact_mod_cast h

end LeanProofs.GowersSzemeredi
