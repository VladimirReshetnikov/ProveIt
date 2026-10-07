import GowersSzemeredi.Proofs03Equivalences
import Mathlib.Algebra.BigOperators.Expect

/-! Unit-modulus normalization for the near-maximal endpoint argument.
The pointwise cube-defect comparison has factor two independent of the
number of derivative directions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def endpointUnitPhase (z : Complex) : Complex := if z = 0 then 1 else z / (‖z‖ : Complex)

theorem endpointUnitPhase_norm (z : Complex) : ‖endpointUnitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [endpointUnitPhase, hz]
  · simp [endpointUnitPhase, hz, norm_ne_zero_iff.mpr hz]

theorem endpointUnitPhase_reconstruct (z : Complex) : (‖z‖ : Complex) * endpointUnitPhase z = z := by
  by_cases hz : z = 0
  · simp [endpointUnitPhase, hz]
  · have hn : (‖z‖ : Complex) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    simp only [endpointUnitPhase, if_neg hz]
    field_simp

theorem endpointUnitPhase_distance (z : Complex) (hz : ‖z‖ ≤ 1) :
    ‖z - endpointUnitPhase z‖ = 1 - ‖z‖ := by
  have he : z - endpointUnitPhase z = ((‖z‖ - 1 : Real) : Complex) * endpointUnitPhase z := by
    push_cast
    rw [sub_mul, one_mul, endpointUnitPhase_reconstruct]
  rw [he, norm_mul, endpointUnitPhase_norm, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos (sub_nonpos.mpr hz)]
  ring

theorem endpointUnitPhase_discValued {N : Nat} (f : ZMod N → Complex) :
    DiscValued (fun x => endpointUnitPhase (f x)) := fun x => (endpointUnitPhase_norm (f x)).le

theorem iteratedDifference_unit_norm {N : Nat} (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (a : List (ZMod N)) (x : ZMod N) :
    ‖iteratedDifference g a x‖ = 1 := by
  induction a generalizing x with
  | nil => exact hg x
  | cons r a ih => simp only [iteratedDifference, difference, norm_mul, norm_star, ih, mul_one]

theorem iteratedDifference_unitPhase_reconstruct {N : Nat} (f : ZMod N → Complex)
    (a : List (ZMod N)) (x : ZMod N) :
    (‖iteratedDifference f a x‖ : Complex) *
      iteratedDifference (fun y => endpointUnitPhase (f y)) a x = iteratedDifference f a x := by
  induction a generalizing x with
  | nil => exact endpointUnitPhase_reconstruct (f x)
  | cons r a ih =>
    simp only [iteratedDifference, difference, norm_mul, norm_star, Complex.ofReal_mul]
    calc
      _ = ((‖iteratedDifference f a x‖ : Complex) *
          iteratedDifference (fun y => endpointUnitPhase (f y)) a x) *
        star ((‖iteratedDifference f a (x - r)‖ : Complex) *
          iteratedDifference (fun y => endpointUnitPhase (f y)) a (x - r)) := by
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
        ring
      _ = _ := by rw [ih, ih]

theorem unitPhase_real_defect (A : Real) (u : Complex) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hu : ‖u‖ = 1) : 1 - u.re ≤ 2 * (1 - ((A : Complex) * u).re) := by
  have hu1 : u.re ≤ 1 := (Complex.re_le_norm u).trans_eq hu
  have hul : -1 ≤ u.re := by
    have ht := Complex.re_le_norm (-u)
    simp only [Complex.neg_re, norm_neg, hu] at ht
    linarith only [ht]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hr : 0 ≤ u.re
  · have ht := mul_le_mul_of_nonneg_right hA1 hr
    nlinarith only [ht, hu1]
  · have ht : A * u.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0 (le_of_not_ge hr)
    nlinarith only [ht, hul]

theorem iteratedDifference_unitPhase_defect {N : Nat} (f : ZMod N → Complex)
    (hf : DiscValued f) (a : List (ZMod N)) (x : ZMod N) :
    1 - (iteratedDifference (fun y => endpointUnitPhase (f y)) a x).re ≤
      2 * (1 - (iteratedDifference f a x).re) := by
  have ht := unitPhase_real_defect ‖iteratedDifference f a x‖
    (iteratedDifference (fun y => endpointUnitPhase (f y)) a x) (norm_nonneg _)
    (iteratedDifference_discValued hf a x)
    (iteratedDifference_unit_norm _ (fun y => endpointUnitPhase_norm (f y)) a x)
  rwa [iteratedDifference_unitPhase_reconstruct] at ht

end LeanProofs.GowersSzemeredi
