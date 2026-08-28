import FabiusFunction.FractionalVolterraCalculus
import FabiusFunction.GlobalExtension

/-!
# Fractional Volterra shifts for the Fabius--Rvachev system

The generic order-raising and affine-covariance laws specialize to the exact
fractional dyadic shift of the signed and bounded Fabius functions and to the
fractional bridge from Rvachev's compactly supported function to the bounded
Fabius function.
-/

open scoped Interval Real
open MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-- On a nonnegative endpoint, raising the fractional order of the signed
Fabius extension by one is the same as halving the endpoint and multiplying
by `2 ^ alpha`. -/
theorem fractionalVolterra_add_one_extendedFabius_of_nonneg
    (F : BoundedFabius) (hF : IsFabius F)
    {alpha x : ℝ} (halpha : 0 < alpha) (hx : 0 ≤ x) :
    fractionalVolterra (alpha + 1) 0 (extendedFabius F) x =
      (2 : ℝ) ^ alpha •
        fractionalVolterra alpha 0 (extendedFabius F) (x / 2) := by
  let g : ℝ → ℝ := fun t => extendedFabius F (t / 2)
  have hg : Continuous g :=
    (extendedFabius_contDiff F hF).continuous.comp
      (continuous_id.div_const 2)
  have hderiv (t : ℝ) : HasDerivAt g (extendedFabius F t) t := by
    have hinner : HasDerivAt (fun s : ℝ => s / 2) (2 : ℝ)⁻¹ t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h := (extendedFabius_hasDerivAt F hF (t / 2)).comp t hinner
    have harg : 2 * (t / 2) = t := by ring
    rw [harg] at h
    have hvalue : 2 * extendedFabius F t * (2 : ℝ)⁻¹ =
        extendedFabius F t := by ring
    rw [hvalue] at h
    exact h
  have hshift :
      fractionalVolterra (alpha + 1) 0 (extendedFabius F) x =
        fractionalVolterra alpha 0 g x := by
    apply fractionalVolterra_add_one_deriv_of_eq_zero
      halpha hx hg.continuousOn
    · intro t _ht
      exact (hderiv t).hasDerivWithinAt
    · exact (extendedFabius_contDiff F hF).continuous.intervalIntegrable 0 x
    · dsimp only [g]
      rw [zero_div, extendedFabius_zero F hF]
  have haff := fractionalVolterra_affine
    alpha 0 (x / 2) 2 0 g (by norm_num) (div_nonneg hx (by norm_num))
  have hgcomp : (fun t : ℝ => g (2 * t + 0)) = extendedFabius F := by
    funext t
    dsimp only [g]
    congr 1
    ring
  have hend : 2 * (x / 2) + 0 = x := by ring
  have hbase : (2 : ℝ) * 0 + 0 = 0 := by norm_num
  rw [hbase, hend, hgcomp] at haff
  exact hshift.trans haff

/-- The bounded Fabius function satisfies the same fractional dyadic shift
on its unit interval. -/
theorem fractionalVolterra_add_one_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    {alpha x : ℝ} (halpha : 0 < alpha) (hx : x ∈ Icc (0 : ℝ) 1) :
    fractionalVolterra (alpha + 1) 0 (fabiusReal F) x =
      (2 : ℝ) ^ alpha •
        fractionalVolterra alpha 0 (fabiusReal F) (x / 2) := by
  have hleft :
      fractionalVolterra (alpha + 1) 0 (fabiusReal F) x =
        fractionalVolterra (alpha + 1) 0 (extendedFabius F) x := by
    apply fractionalVolterra_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact (extendedFabius_eq_fabiusReal F hF
      ⟨ht.1, ht.2.trans hx.2⟩).symm
  have hxhalf : 0 ≤ x / 2 := div_nonneg hx.1 (by norm_num)
  have hright :
      fractionalVolterra alpha 0 (extendedFabius F) (x / 2) =
        fractionalVolterra alpha 0 (fabiusReal F) (x / 2) := by
    apply fractionalVolterra_congr
    intro t ht
    rw [uIcc_of_le hxhalf] at ht
    apply extendedFabius_eq_fabiusReal F hF
    constructor
    · exact ht.1
    · have hxhalf_one : x / 2 ≤ 1 := by
        calc
          x / 2 ≤ 1 / 2 :=
            (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hx.2
          _ ≤ 1 := by norm_num
      exact ht.2.trans hxhalf_one
  calc
    fractionalVolterra (alpha + 1) 0 (fabiusReal F) x =
        fractionalVolterra (alpha + 1) 0 (extendedFabius F) x := hleft
    _ = (2 : ℝ) ^ alpha •
          fractionalVolterra alpha 0 (extendedFabius F) (x / 2) :=
      fractionalVolterra_add_one_extendedFabius_of_nonneg F hF halpha hx.1
    _ = (2 : ℝ) ^ alpha •
          fractionalVolterra alpha 0 (fabiusReal F) (x / 2) := by
      rw [hright]

/-- Fractionally integrating Rvachev's function from its left support
boundary is equivalent, after raising the order by one, to fractionally
integrating the bounded Fabius function at the corresponding half-scale. -/
theorem fractionalVolterra_add_one_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    {alpha x : ℝ} (halpha : 0 < alpha) (hx : -1 ≤ x) :
    fractionalVolterra (alpha + 1) (-1) (rvachevUp F) x =
      (2 : ℝ) ^ alpha •
        fractionalVolterra alpha 0 (fabiusReal F) ((x + 1) / 2) := by
  let g : ℝ → ℝ := fun t => fabiusReal F ((t + 1) / 2)
  have hg : Continuous g := hF.contDiff.continuous.comp
    ((continuous_id.add continuous_const).div_const 2)
  have hshift :
      fractionalVolterra (alpha + 1) (-1) (rvachevUp F) x =
        fractionalVolterra alpha (-1) g x := by
    apply fractionalVolterra_add_one_deriv_of_eq_zero
      halpha hx hg.continuousOn
    · intro t _ht
      exact (hasDerivAt_fabiusReal_half_shift F hF t).hasDerivWithinAt
    · exact (rvachev_contDiff F hF).continuous.intervalIntegrable (-1) x
    · dsimp only [g]
      rw [show ((-1 : ℝ) + 1) / 2 = 0 by norm_num,
        hF.zero_of_nonpos 0 le_rfl]
  have hxhalf : 0 ≤ (x + 1) / 2 := by linarith
  have haff := fractionalVolterra_affine
    alpha 0 ((x + 1) / 2) 2 (-1) g (by norm_num) hxhalf
  have hgcomp : (fun t : ℝ => g (2 * t + (-1))) = fabiusReal F := by
    funext t
    dsimp only [g]
    congr 1
    ring
  have hend : 2 * ((x + 1) / 2) + (-1) = x := by ring
  have hbase : (2 : ℝ) * 0 + (-1) = -1 := by norm_num
  rw [hbase, hend, hgcomp] at haff
  exact hshift.trans haff

end Fabius
