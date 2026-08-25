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

The half-neighborhood is not needed: because the bounded function is constant
on each of the two tails, the estimates in fact hold on the full neighborhood
filters `nhds 0` and `nhds 1`.  Those are `fabiusReal_isLittleO_pow_at_zero`
and `one_sub_fabiusReal_isLittleO_pow_at_one`; the older one-sided names are
retained unchanged for existing call sites.
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

/-- The bounded Fabius function is little-o of every power at zero, from
both sides.

The one-sided restriction in `fabiusReal_isLittleO_pow_at_zero_right` is an
artifact of its proof, not of the mathematics: `fabiusReal F` vanishes
identically on `(-∞, 0]`, so on the missing side both sides of the estimate
are zero.  Concretely, `fabiusReal F` agrees with `extendedFabius F` on the
whole of `(-∞, 1)`, which is a full neighborhood of the origin, so the
two-sided statement for the extension transfers verbatim. -/
theorem fabiusReal_isLittleO_pow_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F =o[nhds 0] (fun x : ℝ => x ^ n) := by
  refine (extendedFabius_isLittleO_pow_at_zero F hF n).congr' ?_
    (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
  by_cases hy0 : y ≤ 0
  · rw [extendedFabius_eq_zero_of_nonpos F hF hy0, hF.zero_of_nonpos y hy0]
  · exact extendedFabius_eq_fabiusReal F hF
      ⟨le_of_lt (lt_of_not_ge hy0), le_of_lt hy⟩

/-- Canonical form of two-sided flatness at zero for the chosen Fabius
function. -/
theorem fabius_isLittleO_pow_at_zero (n : ℕ) :
    fabiusReal fabius =o[nhds 0] (fun x : ℝ => x ^ n) :=
  fabiusReal_isLittleO_pow_at_zero fabius fabius_spec n

/-- From the right, the bounded Fabius function is little-o of every power
at zero.

Kept as stated, with its original proof, so that existing call sites are
untouched; `fabiusReal_isLittleO_pow_at_zero` is the strictly stronger
two-sided form. -/
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

/-- The complementary bounded Fabius function is little-o of every power of
the distance to one, from both sides.

As at the origin, the one-sided restriction in
`one_sub_fabiusReal_isLittleO_pow_at_one_left` is an artifact of the proof:
`fabiusReal F` is identically one on `[1, ∞)`, so `1 - fabiusReal F` vanishes
on the missing side.  The proof is the reflection `x ↦ 1 - x` applied to the
two-sided flatness at zero; the reflection is a homeomorphism carrying
`nhds 1` to `nhds 0`, which is why no half-line has to be carried along. -/
theorem one_sub_fabiusReal_isLittleO_pow_at_one
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal F x) =o[nhds 1] (fun x : ℝ => (1 - x) ^ n) := by
  have hreflect : Tendsto (fun x : ℝ => 1 - x) (nhds (1 : ℝ)) (nhds (0 : ℝ)) := by
    have hcontinuous : Continuous (fun x : ℝ => 1 - x) := by fun_prop
    have hat : Tendsto (fun x : ℝ => 1 - x) (nhds (1 : ℝ))
        (nhds (1 - (1 : ℝ))) :=
      hcontinuous.continuousAt
    simpa using hat
  have h := (fabiusReal_isLittleO_pow_at_zero F hF n).comp_tendsto hreflect
  apply h.congr'
  · exact Filter.Eventually.of_forall fun x => hF.symmetry_all x
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Canonical form of two-sided flatness at one for the chosen Fabius
function. -/
theorem one_sub_fabius_isLittleO_pow_at_one (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal fabius x) =o[nhds 1]
      (fun x : ℝ => (1 - x) ^ n) :=
  one_sub_fabiusReal_isLittleO_pow_at_one fabius fabius_spec n

/-- From the left, the complementary bounded Fabius function is little-o of
every power of the distance to one.

Kept as stated, with its original proof, so that existing call sites are
untouched; `one_sub_fabiusReal_isLittleO_pow_at_one` is the strictly stronger
two-sided form. -/
theorem one_sub_fabiusReal_isLittleO_pow_at_one_left
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal F x) =o[nhdsWithin 1 (Iic 1)]
      (fun x : ℝ => (1 - x) ^ n) := by
  have hreflect : Tendsto (fun x : ℝ => 1 - x)
      (nhdsWithin 1 (Iic 1)) (nhdsWithin 0 (Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcontinuous : Continuous (fun x : ℝ => 1 - x) := by fun_prop
      have hat : Tendsto (fun x : ℝ => 1 - x) (nhds (1 : ℝ))
          (nhds (1 - (1 : ℝ))) :=
        hcontinuous.continuousAt
      have hat' : Tendsto (fun x : ℝ => 1 - x) (nhds (1 : ℝ))
          (nhds (0 : ℝ)) := by simpa using hat
      exact hat'.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 ≤ 1 - x
      exact sub_nonneg.mpr (show x ≤ (1 : ℝ) from hx)
  have h := (fabiusReal_isLittleO_pow_at_zero_right F hF n).comp_tendsto
    hreflect
  apply h.congr'
  · exact Filter.Eventually.of_forall fun x => hF.symmetry_all x
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Canonical form of left-hand flatness at one. -/
theorem one_sub_fabius_isLittleO_pow_at_one_left (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal fabius x) =o[nhdsWithin 1 (Iic 1)]
      (fun x : ℝ => (1 - x) ^ n) :=
  one_sub_fabiusReal_isLittleO_pow_at_one_left fabius fabius_spec n

end Fabius
