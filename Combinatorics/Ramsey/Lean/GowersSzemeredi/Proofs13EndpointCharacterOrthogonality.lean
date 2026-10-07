import GowersSzemeredi.Proofs13EndpointCharacterApproximation

/-! Orthogonality and shifts of scalar unit characters, together with
squared-error stability of a product of unit-modulus functions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpointFourierCoefficient_character {N : Nat} [NeZero N]
    (z : Complex) (r s : ZMod N) :
    endpointFourierCoefficient (endpointCharacter z r) s = if r = s then z else 0 := by
  rw [endpointFourierCoefficient_eq_expect]
  have he (x : ZMod N) : exponential ((-s) * x) * endpointCharacter z r x =
      z * exponential ((r - s) * x) := by
    rw [sub_mul, sub_eq_add_neg, endpoint_exponential_add]
    dsimp [endpointCharacter]
    rw [neg_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_expect, fejer_expect_exponential_mul]
  split_ifs with h <;> simp_all [sub_eq_zero]

theorem endpointCharacter_orthogonality {N : Nat} [NeZero N]
    (z w : Complex) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (r s : ZMod N) (hrs : r ≠ s) :
    endpointL2Error (endpointCharacter z r) (endpointCharacter w s) = 2 := by
  rw [endpointL2Error_character _ (endpointCharacter_norm z hz r) w hw,
    endpointFourierCoefficient_character, if_neg hrs]
  simp

theorem endpointCharacter_shift_product {N : Nat} [NeZero N]
    (z w : Complex) (r s h x : ZMod N) :
    endpointCharacter z r (x - h) * endpointCharacter w s x =
      endpointCharacter (z * w * exponential (-(r * h))) (r + s) x := by
  simp only [endpointCharacter]
  rw [mul_sub, add_mul]
  simp only [sub_eq_add_neg, endpoint_exponential_add]
  ring

theorem endpoint_unit_product_distance (u v a b : Complex) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) :
    ‖u * v - a * b‖ ≤ ‖u - a‖ + ‖v - b‖ := by
  calc
    _ = ‖(u - a) * v + a * (v - b)‖ := by congr 1; ring
    _ ≤ ‖(u - a) * v‖ + ‖a * (v - b)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, hv, ha, mul_one, one_mul]

theorem endpoint_unit_product_error (u v a b c : Complex) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) :
    ‖c - a * b‖ ^ 2 ≤ 3 * (‖c - u * v‖ ^ 2 + ‖u - a‖ ^ 2 + ‖v - b‖ ^ 2) := by
  have ht : ‖c - a * b‖ ≤ ‖c - u * v‖ + ‖u - a‖ + ‖v - b‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub c (u * v) (a * b)
    have hp := endpoint_unit_product_distance u v a b hv ha
    linarith only [h, hp]
  have hn := norm_nonneg (c - a * b)
  have hsq := sq_le_sq₀ hn (by positivity : 0 ≤ ‖c - u * v‖ + ‖u - a‖ + ‖v - b‖)
  have hs := hsq.mpr ht
  nlinarith only [hs, sq_nonneg (‖c - u * v‖ - ‖u - a‖),
    sq_nonneg (‖c - u * v‖ - ‖v - b‖), sq_nonneg (‖u - a‖ - ‖v - b‖)]

end LeanProofs.GowersSzemeredi
