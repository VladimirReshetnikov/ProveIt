import FabiusFunction.Paper06487Supplement
import Mathlib.Analysis.Calculus.Taylor

/-!
# Flatness of the Fabius function at the origin

The signed global extension is smooth and all of its derivatives vanish at
zero.  Taylor's theorem therefore implies that it is smaller than every
power at the origin.  Restricting to the nonnegative half-neighborhood gives
the corresponding statement for the bounded Fabius function.

This is the rigorous local consequence used in the asymptotic drafts when
they say that the Fabius function approaches zero faster than any power.
-/

set_option autoImplicit false

open Set

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

/-- From the right, the bounded Fabius function is little-o of every power
at zero. -/
theorem fabiusReal_isLittleO_pow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F =o[nhdsWithin 0 (Ici 0)] (fun x : ℝ => x ^ n) := by
  have h : extendedFabius F =o[nhdsWithin 0 (Ici 0)]
      (fun x : ℝ => x ^ n) :=
    (extendedFabius_isLittleO_pow_at_zero F hF n).mono
      (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
  refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  have hlt : ∀ᶠ x : ℝ in nhdsWithin 0 (Ici 0), x < 1 :=
    Filter.Eventually.filter_mono
      (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hltx
  exact extendedFabius_eq_fabiusReal F hF ⟨hx, hltx.le⟩

/-- Canonical form of right-hand flatness for the chosen Fabius function. -/
theorem fabius_isLittleO_pow_at_zero_right (n : ℕ) :
    fabiusReal fabius =o[nhdsWithin 0 (Ici 0)] (fun x : ℝ => x ^ n) :=
  fabiusReal_isLittleO_pow_at_zero_right fabius fabius_spec n

end Fabius
