/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.UnitBoxAmplitude

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

structure SlicedProductBlock (ι : Type*) where
  coefficient : ℝ
  lower : ι → ℝ
  width : ι → ℝ
  lastLower : ℝ
  lastWidth : ℝ

namespace SlicedProductBlock

variable {ι : Type*} [Fintype ι]

structure Admissible (B : SlicedProductBlock ι) : Prop where
  coefficient_ne_zero : B.coefficient ≠ 0
  lower_nonneg : ∀ i, 0 ≤ B.lower i
  width_pos : ∀ i, 0 < B.width i
  lastWidth_pos : 0 < B.lastWidth

noncomputable def prefixProduct (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  ∏ i, (B.lower i + B.width i * x i)

noncomputable def value (B : SlicedProductBlock ι) (x : ι → ℝ) (u : ℝ) : ℝ :=
  B.coefficient * B.prefixProduct x * (B.lastLower + B.lastWidth * u)

noncomputable def slope (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastWidth * B.prefixProduct x

noncomputable def base (B : SlicedProductBlock ι) (x : ι → ℝ) : ℝ :=
  B.coefficient * B.lastLower * B.prefixProduct x

noncomputable def volumeScale (B : SlicedProductBlock ι) : ℝ :=
  |B.coefficient| * B.lastWidth * ∏ i, B.width i

theorem value_eq (B : SlicedProductBlock ι) (x : ι → ℝ) (u : ℝ) :
    B.value x u = B.base x + B.slope x * u := by
  unfold value base slope
  ring

theorem prefixProduct_continuous (B : SlicedProductBlock ι) : Continuous B.prefixProduct := by
  unfold prefixProduct
  fun_prop

theorem slope_continuous (B : SlicedProductBlock ι) : Continuous B.slope :=
  continuous_const.mul B.prefixProduct_continuous

theorem base_continuous (B : SlicedProductBlock ι) : Continuous B.base :=
  continuous_const.mul B.prefixProduct_continuous

theorem volumeScale_pos {B : SlicedProductBlock ι} (hB : B.Admissible) : 0 < B.volumeScale :=
  mul_pos (mul_pos (abs_pos.mpr hB.coefficient_ne_zero) hB.lastWidth_pos)
    (Finset.prod_pos (fun i _ => hB.width_pos i))

theorem prefixProduct_nonneg {B : SlicedProductBlock ι} (hB : B.Admissible)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ B.prefixProduct x :=
  Finset.prod_nonneg (fun i _ => add_nonneg (hB.lower_nonneg i)
    (mul_nonneg (hB.width_pos i).le (hx i).1.le))

theorem slope_lower {B : SlicedProductBlock ι} (hB : B.Admissible)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) :
    B.volumeScale * (∏ i, x i) ≤ |B.slope x| := by
  have hp : (∏ i, B.width i) * (∏ i, x i) ≤ B.prefixProduct x := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (hB.width_pos i).le (hx i).1.le)
      (fun i _ => le_add_of_nonneg_left (hB.lower_nonneg i))
  have h := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (abs_nonneg B.coefficient) hB.lastWidth_pos.le)
  simpa only [volumeScale, slope, abs_mul, abs_of_pos hB.lastWidth_pos,
    abs_of_nonneg (prefixProduct_nonneg hB hx), mul_assoc] using h

theorem volumeScale_lower {B : SlicedProductBlock ι} {c δ : ℝ} (_hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hcoeff : c ≤ |B.coefficient|) (hlast : δ ≤ B.lastWidth) (hwidth : ∀ i, δ ≤ B.width i) :
    c * δ ^ (Fintype.card ι + 1) ≤ B.volumeScale := by
  have hp : δ ^ Fintype.card ι ≤ ∏ i, B.width i := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => hδ) (fun i _ => hwidth i)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  have h := mul_le_mul (mul_le_mul hcoeff hlast hδ (abs_nonneg _)) hp
    (pow_nonneg hδ _) (mul_nonneg (abs_nonneg _) (hδ.trans hlast))
  simpa only [volumeScale, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

end SlicedProductBlock

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairScale (A B : SlicedProductBlock ι) : ℝ := min A.volumeScale B.volumeScale

noncomputable def pairWidth (A B : SlicedProductBlock ι) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max |A.slope p.1| |B.slope p.2|

theorem pairScale_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairScale A B := lt_min (volumeScale_pos hA) (volumeScale_pos hB)

theorem pairWidth_measurable (A B : SlicedProductBlock ι) : Measurable (pairWidth A B) :=
  ((A.slope_continuous.measurable.comp measurable_fst).abs).max
    (B.slope_continuous.measurable.comp measurable_snd).abs

theorem pairWidth_lower {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      pairScale A B * pairedAmplitude p ≤ pairWidth A B p := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (unitBoxMeasure_ae (ι := ι)),
    Measure.quasiMeasurePreserving_snd.ae (unitBoxMeasure_ae (ι := ι))] with p hp hq
  have hleft : pairScale A B * (∏ i, p.1 i) ≤ |A.slope p.1| :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Finset.prod_nonneg (fun i _ => (hp i).1.le))).trans
      (slope_lower hA hp)
  have hright : pairScale A B * (∏ i, p.2 i) ≤ |B.slope p.2| :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Finset.prod_nonneg (fun i _ => (hq i).1.le))).trans
      (slope_lower hB hq)
  change pairScale A B * max (∏ i, p.1 i) (∏ i, p.2 i) ≤ _
  rw [mul_max_of_nonneg _ _ (pairScale_pos hA hB).le]
  exact max_le_max hleft hright

theorem pairWidth_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι), 0 < pairWidth A B p := by
  filter_upwards [pairWidth_lower hA hB, pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  exact (mul_pos (pairScale_pos hA hB) hpos).trans_le hp

theorem pairWidth_inverse_bound {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    ∀ᵐ p ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι),
      (pairWidth A B p)⁻¹ ≤ (pairScale A B)⁻¹ * (pairedAmplitude p)⁻¹ := by
  filter_upwards [pairWidth_lower hA hB, pairedAmplitude_pos_ae (ι := ι)] with p hp hpos
  have hlow := mul_pos (pairScale_pos hA hB) hpos
  rw [← mul_inv]
  exact (inv_le_inv₀ (hlow.trans_le hp) hlow).mpr hp

theorem pairWidth_inverse_integrable {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    Integrable (fun p => (pairWidth A B p)⁻¹) ((unitBoxMeasure ι).prod (unitBoxMeasure ι)) := by
  apply (pairedAmplitude_inverse_integrable.const_mul (pairScale A B)⁻¹).mono'
    (pairWidth_measurable A B).inv.aestronglyMeasurable
  filter_upwards [pairWidth_inverse_bound hA hB, pairWidth_pos hA hB] with p hp hpos
  change ‖(pairWidth A B p)⁻¹‖ ≤ _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact hp

noncomputable def pairCap (A B : SlicedProductBlock ι) : ℝ :=
  (pairScale A B)⁻¹ * 4 ^ Fintype.card ι

theorem pairCap_pos {A B : SlicedProductBlock ι} (hA : A.Admissible) (hB : B.Admissible) :
    0 < pairCap A B := mul_pos (inv_pos.mpr (pairScale_pos hA hB)) (by positivity)

theorem pairWidth_inverse_integral_le {A B : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) :
    (∫ p, (pairWidth A B p)⁻¹ ∂(unitBoxMeasure ι).prod (unitBoxMeasure ι)) ≤ pairCap A B := by
  have h := integral_mono_ae (pairWidth_inverse_integrable hA hB)
    (pairedAmplitude_inverse_integrable.const_mul (pairScale A B)⁻¹) (pairWidth_inverse_bound hA hB)
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left pairedAmplitude_inverse_integral_le
    (inv_nonneg.mpr (pairScale_pos hA hB).le))

theorem pairCap_le_of_scale_lower {A B : SlicedProductBlock ι} {r : ℝ}
    (hr : 0 < r) (hA : r ≤ A.volumeScale) (hB : r ≤ B.volumeScale) :
    pairCap A B ≤ r⁻¹ * 4 ^ Fintype.card ι := by
  have hscale : r ≤ pairScale A B := le_min hA hB
  exact mul_le_mul_of_nonneg_right
    ((inv_le_inv₀ (hr.trans_le hscale) hr).mpr hscale) (by positivity)

end Erdos3.SlicedProductBlock

end

end OAI
