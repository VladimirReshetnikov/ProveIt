import FabiusFunction.Paper06487Supplement
import Mathlib.Analysis.Calculus.Taylor

/-!
# Flatness of the Fabius function at the origin

The signed global extension is smooth and all of its derivatives vanish at
zero.  Taylor's theorem therefore implies that it is smaller than every
power at the origin.  Near zero the bounded function either agrees with that
extension or vanishes identically, giving genuine two-sided flatness.  Its
reflection gives the corresponding two-sided statement at one; the original
one-sided formulations remain as compatibility corollaries.

This is the rigorous local consequence used in the asymptotic drafts when
they say that the Fabius function approaches zero faster than any power.
-/

set_option autoImplicit false

open Filter Set

namespace Fabius

private theorem taylorWithinEval_extendedFabius_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    taylorWithinEval (extendedFabius F) n univ 0 x = 0 := by
  induction n with
  | zero =>
      have hzero : extendedFabius F 0 = 0 :=
        extendedFabius_eq_zero_of_nonpos F hF (by norm_num)
      simpa [taylorWithinEval, taylorWithin, taylorCoeffWithin] using hzero
  | succ n ih =>
      rw [taylorWithinEval_succ, ih]
      rw [iteratedDerivWithin_eq_iteratedDeriv]
      · rw [iteratedDeriv_extendedFabius_zero F hF]
        simp
      · exact uniqueDiffOn_univ
      · exact (extendedFabius_contDiff F hF).contDiffAt.of_le
          (by exact WithTop.coe_le_coe.mpr le_top)
      · simp

/-- The signed global Fabius extension is little-o of every power at zero. -/
theorem extendedFabius_isLittleO_pow_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    extendedFabius F =o[nhds 0] (fun x : ℝ => x ^ n) := by
  have hsmooth : ContDiff ℝ n (extendedFabius F) :=
    (extendedFabius_contDiff F hF).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)
  have h := taylor_isLittleO_univ (x₀ := (0 : ℝ)) hsmooth
  simp_rw [taylorWithinEval_extendedFabius_zero F hF n] at h
  simpa using h

/-- The bounded Fabius function is little-o of every power in a full
neighborhood of zero.  On the left it vanishes identically, while near zero
on the right it agrees with the signed extension. -/
theorem fabiusReal_isLittleO_pow_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F =o[nhds 0] (fun x : ℝ => x ^ n) := by
  refine (extendedFabius_isLittleO_pow_at_zero F hF n).congr' ?_
    (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  by_cases hx0 : x ≤ 0
  · rw [extendedFabius_eq_zero_of_nonpos F hF hx0,
      hF.zero_of_nonpos x hx0]
  · exact extendedFabius_eq_fabiusReal F hF
      ⟨le_of_lt (lt_of_not_ge hx0), hx.le⟩

/-- From the right, the bounded Fabius function is little-o of every power
at zero. -/
theorem fabiusReal_isLittleO_pow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F =o[nhdsWithin 0 (Ici 0)] (fun x : ℝ => x ^ n) := by
  exact (fabiusReal_isLittleO_pow_at_zero F hF n).mono
    (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))

/-- Canonical two-sided flatness at zero for the chosen Fabius function. -/
theorem fabius_isLittleO_pow_at_zero (n : ℕ) :
    fabiusReal fabius =o[nhds 0] (fun x : ℝ => x ^ n) :=
  fabiusReal_isLittleO_pow_at_zero fabius fabius_spec n

/-- Canonical form of right-hand flatness for the chosen Fabius function. -/
theorem fabius_isLittleO_pow_at_zero_right (n : ℕ) :
    fabiusReal fabius =o[nhdsWithin 0 (Ici 0)] (fun x : ℝ => x ^ n) :=
  fabiusReal_isLittleO_pow_at_zero_right fabius fabius_spec n

/-- The complementary bounded Fabius function is little-o of every power of
the distance to one in a full neighborhood of that endpoint. -/
theorem one_sub_fabiusReal_isLittleO_pow_at_one
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal F x) =o[nhds 1]
      (fun x : ℝ => (1 - x) ^ n) := by
  have hcontinuous : Continuous (fun x : ℝ => 1 - x) := by fun_prop
  have hreflect : Tendsto (fun x : ℝ => 1 - x)
      (nhds (1 : ℝ)) (nhds (0 : ℝ)) := by
    have hat : Tendsto (fun x : ℝ => 1 - x)
        (nhds (1 : ℝ)) (nhds (1 - (1 : ℝ))) :=
      hcontinuous.continuousAt
    simpa only [sub_self] using hat
  have h := (fabiusReal_isLittleO_pow_at_zero F hF n).comp_tendsto hreflect
  apply h.congr'
  · exact Filter.Eventually.of_forall fun x => hF.symmetry_all x
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- From the left, the complementary bounded Fabius function is little-o of
every power of the distance to one. -/
theorem one_sub_fabiusReal_isLittleO_pow_at_one_left
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal F x) =o[nhdsWithin 1 (Iic 1)]
      (fun x : ℝ => (1 - x) ^ n) := by
  exact (one_sub_fabiusReal_isLittleO_pow_at_one F hF n).mono
    (nhdsWithin_le_nhds (s := Iic (1 : ℝ)))

/-- Canonical two-sided flatness at one for the chosen Fabius function. -/
theorem one_sub_fabius_isLittleO_pow_at_one (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal fabius x) =o[nhds 1]
      (fun x : ℝ => (1 - x) ^ n) :=
  one_sub_fabiusReal_isLittleO_pow_at_one fabius fabius_spec n

/-- Canonical form of left-hand flatness at one. -/
theorem one_sub_fabius_isLittleO_pow_at_one_left (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal fabius x) =o[nhdsWithin 1 (Iic 1)]
      (fun x : ℝ => (1 - x) ^ n) :=
  one_sub_fabiusReal_isLittleO_pow_at_one_left fabius fabius_spec n

end Fabius
