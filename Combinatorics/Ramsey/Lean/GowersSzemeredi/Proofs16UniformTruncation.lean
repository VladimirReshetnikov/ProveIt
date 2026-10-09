import GowersSzemeredi.Proofs16FourierTail

/-! Uniform Fourier truncation for the discrete trapezoid. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Keep only frequencies with centered absolute value at most R. -/
def centeredFourierTruncation {N : Nat} [NeZero N] (f : ZMod N → Complex)
    (R : Nat) (x : ZMod N) : Complex :=
  (N : Complex)⁻¹ * ∑ r ∈ centeredBall N R, fourier f r * exponential (r * x)

/-- Fourier inversion bounds the uniform truncation error by the normalized
sum of the omitted coefficient norms. -/
theorem centeredFourierTruncation_error {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (R : Nat) (x : ZMod N) :
    ‖f x - centeredFourierTruncation f R x‖ ≤
      (N : Real)⁻¹ * ∑ r ∈ Finset.univ.filter (fun r : ZMod N => R < centeredAbs r),
        ‖fourier f r‖ := by
  have hsplit : (∑ r : ZMod N, fourier f r * exponential (r * x)) =
      (∑ r ∈ centeredBall N R, fourier f r * exponential (r * x)) +
      ∑ r ∈ Finset.univ.filter (fun r : ZMod N => R < centeredAbs r),
        fourier f r * exponential (r * x) := by
    simpa only [centeredBall, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : ZMod N => centeredAbs r ≤ R)
        (fun r => fourier f r * exponential (r * x))).symm
  rw [identity_2_4_holds N f x, centeredFourierTruncation, ← mul_sub, hsplit,
    add_sub_cancel_left, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul, show ‖exponential (r * x)‖ = 1 from (ZMod.stdAddChar (N := N)).norm_apply _, mul_one]

/-- The trapezoid has a uniform, explicit finite truncation bound. -/
theorem trapezoid_uniform_truncation {N : Nat} [NeZero N] {a c : Nat}
    (ha : 2 * a < N) (hc : 2 * c < N) (R : Nat) (x : ZMod N) :
    ‖((trapezoid a c x : Real) : Complex) -
      centeredFourierTruncation (fun t => ((trapezoid a c t : Real) : Complex)) R x‖ ≤
      N / ((centeredBall N c).card * (R + 1 : Real)) := by
  let f : ZMod N → Complex := fun t => ((trapezoid a c t : Real) : Complex)
  let S := Finset.univ.filter (fun r : ZMod N => R < centeredAbs r)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hC : (0 : Real) < (centeredBall N c).card := by
    have hz : (0 : ZMod N) ∈ centeredBall N c := by simp [centeredBall, centeredAbs]
    exact_mod_cast Finset.card_pos.mpr ⟨0, hz⟩
  have hterm (r : ZMod N) (hr : r ∈ S) : ‖fourier f r‖ ≤
      ((N : Real)^2 / (4 * (centeredBall N c).card)) * (((centeredAbs r : Real)^2)⁻¹) := by
    have habs : 0 < centeredAbs r := lt_of_le_of_lt (Nat.zero_le R) (Finset.mem_filter.mp hr).2
    have hr0 : r ≠ 0 := by intro h; subst r; simp [centeredAbs] at habs
    have h := fourier_trapezoid_le ha hc hr0
    have hpos : (0 : Real) < centeredAbs r := by exact_mod_cast habs
    convert h using 1
    field_simp
    ring
  calc
    _ ≤ (N : Real)⁻¹ * ∑ r ∈ S, ‖fourier f r‖ := centeredFourierTruncation_error f R x
    _ ≤ (N : Real)⁻¹ * ∑ r ∈ S,
        ((N : Real)^2 / (4 * (centeredBall N c).card)) * (((centeredAbs r : Real)^2)⁻¹) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (N : Real)⁻¹ * ((N : Real)^2 / (4 * (centeredBall N c).card)) *
        ∑ r ∈ S, (((centeredAbs r : Real)^2)⁻¹) := by rw [← Finset.mul_sum]; ring
    _ ≤ (N : Real)⁻¹ * ((N : Real)^2 / (4 * (centeredBall N c).card)) * (4 / (R + 1 : Real)) :=
      mul_le_mul_of_nonneg_left (centered_inverse_square_tail R) (by positivity)
    _ = _ := by field_simp

end LeanProofs.GowersSzemeredi
