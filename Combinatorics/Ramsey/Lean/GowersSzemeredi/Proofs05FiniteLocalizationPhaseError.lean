import GowersSzemeredi.Proofs05FiniteLocalizationScale
import GowersSzemeredi.Proofs05QuadraticPhaseError

/-! Uniform control of the leading monomial in every degree. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finiteLocalization_leading_error {k L H : Nat} (hL : 2 ≤ L) (hH : 1 ≤ H) :
    2 * Real.pi * (2 * (H : Real)) ^ k / finiteLocalizationPrecision k L H ≤
      1 / (8 * L) := by
  have hL0 : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hH0 : (0 : Real) < H := by exact_mod_cast (show 0 < H by omega)
  have he : 2 * Real.pi * (2 * (H : Real)) ^ k / finiteLocalizationPrecision k L H =
      Real.pi / (32 * L) := by
    simp only [finiteLocalizationPrecision, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_pow, pow_add]
    norm_num only [show (2 : Real) ^ 6 = 64 by norm_num]
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_le_four]

theorem polynomial_leading_phase_error {N k L H t : Nat} [NeZero N]
    (b y : ZMod N) (hL : 2 ≤ L) (hH : 1 ≤ H)
    (hb : (centeredAbs b : Real) ≤ (N : Real) / finiteLocalizationPrecision k L H)
    (ht : t ≤ 2 * H) :
    ‖exponential (-(b * (t : ZMod N) ^ k + y)) - exponential (-y)‖ ≤
      1 / (8 * L) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hR : (0 : Real) < finiteLocalizationPrecision k L H := by
    exact_mod_cast (show 0 < finiteLocalizationPrecision k L H by
      have := finiteLocalizationPrecision_ge_two (k := k) hL hH; omega)
  have htR : (t : Real) ≤ 2 * (H : Real) := by exact_mod_cast ht
  have hbmul : (centeredAbs (b * (t : ZMod N) ^ k) : Real) ≤
      (centeredAbs b : Real) * (t : Real) ^ k := by
    exact_mod_cast centeredAbs_mul_natCast_pow_le b t k
  rw [exponential_neg_add_distance]
  calc
    _ ≤ 2 * Real.pi * centeredAbs (-(b * (t : ZMod N) ^ k)) / N :=
      downstream_norm_exponential_sub_one_le _
    _ = 2 * Real.pi * centeredAbs (b * (t : ZMod N) ^ k) / N := by
      simp only [centeredAbs, ZMod.natAbs_valMinAbs_neg]
    _ ≤ 2 * Real.pi * ((N : Real) / finiteLocalizationPrecision k L H *
          (2 * (H : Real)) ^ k) / N := by
      gcongr
      exact hbmul.trans (mul_le_mul hb (pow_le_pow_left₀ (by positivity) htR k)
        (by positivity) (by positivity))
    _ = 2 * Real.pi * (2 * (H : Real)) ^ k / finiteLocalizationPrecision k L H := by field_simp
    _ ≤ _ := finiteLocalization_leading_error hL hH

end LeanProofs.GowersSzemeredi
