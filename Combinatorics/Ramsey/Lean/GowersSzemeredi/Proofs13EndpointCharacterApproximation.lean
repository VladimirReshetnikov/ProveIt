import GowersSzemeredi.Proofs13EndpointFrequencyMap

/-! Unit scalar characters approximating the dominant Fourier mode.
The squared mean error is exactly twice the Fourier modulus defect. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointL2Error {A : Type*} [Fintype A] (f g : A → Complex) : Real :=
  𝔼 x : A, ‖f x - g x‖ ^ 2

theorem endpointL2Error_nonneg {A : Type*} [Fintype A] (f g : A → Complex) :
    0 ≤ endpointL2Error f g := Finset.expect_nonneg (fun _ _ => sq_nonneg _)

theorem endpoint_expect_re {A : Type*} [Fintype A] (f : A → Complex) :
    (𝔼 x : A, f x).re = 𝔼 x : A, (f x).re := by
  simp [Finset.expect, Complex.re_sum]

theorem endpoint_exponential_add {N : Nat} [NeZero N] (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y :=
  AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

theorem endpoint_exponential_star {N : Nat} [NeZero N] (x : ZMod N) :
    star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

theorem endpoint_exponential_norm {N : Nat} [NeZero N] (x : ZMod N) :
    ‖exponential x‖ = 1 := (ZMod.stdAddChar (N := N)).norm_apply x

def endpointCharacter {N : Nat} [NeZero N] (z : Complex) (r x : ZMod N) : Complex :=
  z * exponential (r * x)

theorem endpointCharacter_norm {N : Nat} [NeZero N] (z : Complex) (hz : ‖z‖ = 1)
    (r x : ZMod N) : ‖endpointCharacter z r x‖ = 1 := by
  simp only [endpointCharacter, norm_mul, hz, endpoint_exponential_norm, one_mul]

theorem endpoint_unit_norm_distance (u v : Complex) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ^ 2 = 2 - 2 * (u * star v).re := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hu, hv, Complex.star_def]
  ring

theorem endpointL2Error_character {N : Nat} [NeZero N] (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (z : Complex) (hz : ‖z‖ = 1) (r : ZMod N) :
    endpointL2Error g (endpointCharacter z r) =
      2 - 2 * (star z * endpointFourierCoefficient g r).re := by
  unfold endpointL2Error
  simp_rw [endpoint_unit_norm_distance _ _ (hg _) (endpointCharacter_norm z hz r _)]
  rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.mul_expect,
    ← endpoint_expect_re, endpointFourierCoefficient_eq_expect, Finset.mul_expect]
  congr 3
  apply Finset.expect_congr rfl
  intro x _
  simp only [endpointCharacter, star_mul, endpoint_exponential_star, neg_mul]
  ring

theorem endpointUnitPhase_correlation (w : Complex) :
    star (endpointUnitPhase w) * w = (‖w‖ : Complex) := by
  conv_lhs => rhs; rw [← endpointUnitPhase_reconstruct w]
  have hu : star (endpointUnitPhase w) * endpointUnitPhase w = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, endpointUnitPhase_norm]
    norm_num
  calc
    _ = (‖w‖ : Complex) * (star (endpointUnitPhase w) * endpointUnitPhase w) := by ring
    _ = _ := by rw [hu, mul_one]

def endpointApproximatingCharacter {N : Nat} [NeZero N] (g : ZMod N → Complex) : ZMod N → Complex :=
  endpointCharacter (endpointUnitPhase (endpointFourierCoefficient g (endpointDominantFrequency g)))
    (endpointDominantFrequency g)

theorem endpointApproximatingCharacter_norm {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (x : ZMod N) : ‖endpointApproximatingCharacter g x‖ = 1 :=
  endpointCharacter_norm _ (endpointUnitPhase_norm _) _ _

theorem endpointApproximatingCharacter_error {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    endpointL2Error g (endpointApproximatingCharacter g) =
      2 - 2 * ‖endpointFourierCoefficient g (endpointDominantFrequency g)‖ := by
  unfold endpointApproximatingCharacter
  rw [endpointL2Error_character g hg _ (endpointUnitPhase_norm _),
    endpointUnitPhase_correlation, Complex.ofReal_re]

theorem endpointApproximatingCharacter_error_le {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    endpointL2Error g (endpointApproximatingCharacter g) ≤ 2 * (1 - endpointCubeMean g 2) := by
  rw [endpointApproximatingCharacter_error g hg]
  have hc := endpointDominantFrequency_concentration g hg
  have hb := endpointFourierCoefficient_norm_le_one g (fun x => (hg x).le) (endpointDominantFrequency g)
  have hn := norm_nonneg (endpointFourierCoefficient g (endpointDominantFrequency g))
  nlinarith only [hc, hb, hn]

end LeanProofs.GowersSzemeredi
