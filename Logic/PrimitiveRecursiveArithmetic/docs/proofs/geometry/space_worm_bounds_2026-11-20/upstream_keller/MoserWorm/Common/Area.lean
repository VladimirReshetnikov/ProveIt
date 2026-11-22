/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import MoserWorm.Common.Defs
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Planar determinants, triangle area, and the cyclic shoelace identity. -/

open MeasureTheory Complex Set
open scoped ENNReal

namespace MoserWorm

/-- The planar cross product (signed parallelogram area) of two vectors in `Plane`. -/
noncomputable def cross (u v : Plane) : ℝ := u.re * v.im - u.im * v.re

/-- The defining re/im formula for `cross`. -/
@[simp] theorem cross_apply (u v : Plane) : cross u v = u.re * v.im - u.im * v.re := rfl

/-- `cross` is the area form: `cross u v = (conj u * v).im`. -/
theorem cross_eq_im_conj_mul (u v : Plane) : cross u v = ((starRingEnd Plane) u * v).im := by
  simp only [cross_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem cross_self (u : Plane) : cross u u = 0 := by simp only [cross_apply]; ring

theorem cross_swap (u v : Plane) : cross u v = -cross v u := by simp only [cross_apply]; ring

/-- `cross u ·` is `ℝ`-linear. -/
theorem cross_isLinearMap_right (u : Plane) : IsLinearMap ℝ (cross u) := by
  constructor
  · intro x y
    simp only [cross_apply, Complex.add_re, Complex.add_im]
    ring
  · intro t x
    simp only [cross_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring

/-- `cross u ·` bundled as a linear map. -/
noncomputable def crossL (u : Plane) : Plane →ₗ[ℝ] ℝ :=
  IsLinearMap.mk' (cross u) (cross_isLinearMap_right u)

@[simp] theorem crossL_apply (u z : Plane) : crossL u z = cross u z := rfl

theorem cross_smul_right (u : Plane) (t : ℝ) (v : Plane) : cross u (t • v) = t * cross u v := by
  simp only [cross_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-! ### Lines are volume-null -/

/-- A level set of `cross u ·` for `u ≠ 0` (i.e. a line) is Lebesgue-null. -/
theorem volume_setOf_cross_eq (u : Plane) (hu : u ≠ 0) (c : ℝ) :
    volume {z : Plane | cross u z = c} = 0 := by
  -- the squared norm of `u` is positive
  have hN : 0 < u.re * u.re + u.im * u.im := by
    simpa [Complex.normSq_apply] using Complex.normSq_pos.mpr hu
  have hIu : cross u (Complex.I * u) = u.re * u.re + u.im * u.im := by
    simp only [cross_apply, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  -- the kernel line through the origin is null
  have hker : volume {z : Plane | cross u z = 0} = 0 := by
    have hset : {z : Plane | cross u z = 0} = (LinearMap.ker (crossL u) : Set Plane) := by
      ext z
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, crossL_apply]
    rw [hset]
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    have hmem : Complex.I * u ∈ LinearMap.ker (crossL u) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, crossL_apply, hIu] at hmem
    exact absurd hmem (ne_of_gt hN)
  -- translate the level set onto the kernel
  have hcp : cross u ((c / (u.re * u.re + u.im * u.im)) • (Complex.I * u)) = c := by
    rw [cross_smul_right, hIu]
    exact div_mul_cancel₀ c (ne_of_gt hN)
  set p : Plane := (c / (u.re * u.re + u.im * u.im)) • (Complex.I * u) with hp
  have hshift : {z : Plane | cross u z = c} = (fun w => p + w) '' {z : Plane | cross u z = 0} := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · intro hz
      refine ⟨z - p, ?_, by ring⟩
      have e : cross u (z - p) = cross u z - cross u p := by
        simp only [cross_apply, Complex.sub_re, Complex.sub_im]
        ring
      rw [e, hz, hcp, sub_self]
    · rintro ⟨y, hy, rfl⟩
      have e : cross u (p + y) = cross u p + cross u y := by
        simp only [cross_apply, Complex.add_re, Complex.add_im]
        ring
      rw [e, hy, hcp, add_zero]
  have himg : (fun w : Plane => p + w) '' {z : Plane | cross u z = 0}
      = (fun w : Plane => -p + w) ⁻¹' {z : Plane | cross u z = 0} := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨-p + z, hz, by ring⟩
  rw [hshift, himg, measure_preimage_add]
  exact hker

/-- A line through `p` parallel to `u ≠ 0` is Lebesgue-null. -/
theorem volume_cross_line (u p : Plane) (hu : u ≠ 0) :
    volume {z : Plane | cross u (z - p) = 0} = 0 := by
  have h : {z : Plane | cross u (z - p) = 0} = {z : Plane | cross u z = cross u p} := by
    ext z
    have e : cross u (z - p) = cross u z - cross u p := by
      simp only [cross_apply, Complex.sub_re, Complex.sub_im]
      ring
    simp only [Set.mem_ofPred_eq, e, sub_eq_zero]
  rw [h]
  exact volume_setOf_cross_eq u hu _

/-! ### Translation invariance helper -/

private theorem volume_image_add (a : Plane) (s : Set Plane) :
    volume ((fun z => a + z) '' s) = volume s := by
  -- `measure_vadd` (translation invariance) is a default `simp` lemma
  simp

/-! ### The standard triangle -/

/-- The standard triangle with vertices `0`, `1`, `I`. -/
private def stdTriangle : Set Plane := {z : Plane | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1}

/-- The reflected standard triangle (the other half of the unit square). -/
private def stdTriangleR : Set Plane := {z : Plane | z.re ≤ 1 ∧ z.im ≤ 1 ∧ 1 ≤ z.re + z.im}

/-- The unit square `[0,1] × [0,1]` in `Plane`. -/
private def unitSquare : Set Plane :=
  {z : Plane | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1}

private theorem convex_stdTriangle : Convex ℝ stdTriangle := by
  intro x hx y hy s t hs ht hst
  simp only [stdTriangle, Set.mem_ofPred_eq] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg hs hx1) (mul_nonneg ht hy1),
    add_nonneg (mul_nonneg hs hx2) (mul_nonneg ht hy2), ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hx3 hs, mul_le_mul_of_nonneg_left hy3 ht]

private theorem measurableSet_stdTriangle : MeasurableSet stdTriangle := by
  have h1 : MeasurableSet {z : Plane | 0 ≤ z.re} :=
    measurableSet_le measurable_const Complex.measurable_re
  have h2 : MeasurableSet {z : Plane | 0 ≤ z.im} :=
    measurableSet_le measurable_const Complex.measurable_im
  have h3 : MeasurableSet {z : Plane | z.re + z.im ≤ 1} :=
    measurableSet_le (Complex.measurable_re.add Complex.measurable_im) measurable_const
  have h : stdTriangle =
      {z : Plane | 0 ≤ z.re} ∩ ({z : Plane | 0 ≤ z.im} ∩ {z : Plane | z.re + z.im ≤ 1}) := by
    ext z
    simp only [stdTriangle, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  exact h1.inter (h2.inter h3)

private theorem measurableSet_stdTriangleR : MeasurableSet stdTriangleR := by
  have h1 : MeasurableSet {z : Plane | z.re ≤ 1} :=
    measurableSet_le Complex.measurable_re measurable_const
  have h2 : MeasurableSet {z : Plane | z.im ≤ 1} :=
    measurableSet_le Complex.measurable_im measurable_const
  have h3 : MeasurableSet {z : Plane | 1 ≤ z.re + z.im} :=
    measurableSet_le measurable_const (Complex.measurable_re.add Complex.measurable_im)
  have h : stdTriangleR
      = {z : Plane | z.re ≤ 1} ∩ ({z : Plane | z.im ≤ 1} ∩ {z : Plane | 1 ≤ z.re + z.im}) := by
    ext z
    simp only [stdTriangleR, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  exact h1.inter (h2.inter h3)

/-- The standard triangle is the convex hull of `{0, 1, I}`. -/
private theorem stdTriangle_eq_hull : convexHull ℝ ({0, 1, I} : Set Plane) = stdTriangle := by
  apply Subset.antisymm
  · apply convexHull_min _ convex_stdTriangle
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · simp only [stdTriangle, Set.mem_ofPred_eq, Complex.zero_re, Complex.zero_im]
      norm_num
    · simp only [stdTriangle, Set.mem_ofPred_eq, Complex.one_re, Complex.one_im]
      norm_num
    · simp only [stdTriangle, Set.mem_ofPred_eq, Complex.I_re, Complex.I_im]
      norm_num
  · intro z hz
    simp only [stdTriangle, Set.mem_ofPred_eq] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    have h0 : (0 : Plane) ∈ convexHull ℝ ({0, 1, I} : Set Plane) := subset_convexHull ℝ _ (by simp)
    have hone : (1 : Plane) ∈ convexHull ℝ ({0, 1, I} : Set Plane) :=
      subset_convexHull ℝ _ (by simp)
    have hI : I ∈ convexHull ℝ ({0, 1, I} : Set Plane) := subset_convexHull ℝ _ (by simp)
    rcases eq_or_lt_of_le (add_nonneg h1 h2) with heq | hpos
    · have hre : z.re = 0 := by linarith
      have him : z.im = 0 := by linarith
      have hz0 : z = 0 := Complex.ext hre him
      rw [hz0]
      exact h0
    · have hσ0 : z.re + z.im ≠ 0 := ne_of_gt hpos
      have hw : ((z.re / (z.re + z.im)) • (1 : Plane) + (z.im / (z.re + z.im)) • I)
          ∈ convexHull ℝ ({0, 1, I} : Set Plane) :=
        (convex_convexHull ℝ _) hone hI (div_nonneg h1 hpos.le) (div_nonneg h2 hpos.le)
          (by field_simp)
      have hcomb := (convex_convexHull ℝ ({0, 1, I} : Set Plane)) hw h0 hpos.le
        (by linarith : (0 : ℝ) ≤ 1 - (z.re + z.im)) (by ring)
      have hzeq : (z.re + z.im) • ((z.re / (z.re + z.im)) • (1 : Plane)
          + (z.im / (z.re + z.im)) • I) + (1 - (z.re + z.im)) • (0 : Plane) = z := by
        apply Complex.ext <;>
          · simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
              Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.zero_re,
              Complex.zero_im, smul_eq_mul]
            field_simp
            ring
      rw [← hzeq]
      exact hcomb

private theorem volume_unitSquare : volume unitSquare = 1 := by
  have h : unitSquare = Complex.measurableEquivRealProd ⁻¹' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
    ext z
    simp only [unitSquare, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod, Set.mem_ofPred_eq]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  rw [Measure.prod_prod, Real.volume_Icc]
  norm_num

private theorem volume_stdTriangleR : volume stdTriangleR = volume stdTriangle := by
  have h : stdTriangleR =
      (fun z : Plane => -z) ⁻¹' ((fun z : Plane => (1 + I) + z) ⁻¹' stdTriangle) := by
    ext z
    simp only [stdTriangle, stdTriangleR, Set.mem_preimage, Set.mem_ofPred_eq,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith, by linarith, by linarith⟩
  rw [h, show (fun z : Plane => -z) = Neg.neg from rfl, Measure.measure_preimage_neg]
  exact measure_preimage_add volume _ _

/-- The standard triangle has area `1/2`. -/
private theorem volume_stdTriangle : volume stdTriangle = ENNReal.ofReal (1 / 2) := by
  have hunion : stdTriangle ∪ stdTriangleR = unitSquare := by
    ext z
    simp only [stdTriangle, stdTriangleR, unitSquare, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_Icc]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩
      · exact ⟨⟨by linarith, h1⟩, ⟨by linarith, h2⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rcases le_total (z.re + z.im) 1 with h | h
      · exact Or.inl ⟨h1, h3, h⟩
      · exact Or.inr ⟨h2, h4, h⟩
  have hinter : volume (stdTriangle ∩ stdTriangleR) = 0 := by
    apply measure_mono_null _
      (volume_setOf_cross_eq (1 - I) (by norm_num [Complex.ext_iff]) 1)
    rintro z ⟨hz1, hz2⟩
    simp only [stdTriangle, stdTriangleR, Set.mem_ofPred_eq] at hz1 hz2
    obtain ⟨-, -, h3⟩ := hz1
    obtain ⟨-, -, h6⟩ := hz2
    change cross (1 - I) z = 1
    simp only [cross_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im]
    linarith
  have hkey := measure_union_add_inter (μ := volume) stdTriangle measurableSet_stdTriangleR
  rw [hunion, hinter, volume_unitSquare, add_zero, volume_stdTriangleR] at hkey
  -- hkey : 1 = volume stdTriangle + volume stdTriangle
  have hfin : volume stdTriangle ≠ ⊤ := by
    intro htop
    rw [htop] at hkey
    simp at hkey
  have h2 := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at h2
  rw [← ENNReal.ofReal_toReal hfin, show (volume stdTriangle).toReal = 1 / 2 by linarith]

/-! ### The linear map sending the standard triangle to a general triangle -/

/-- The `ℝ`-linear map on `Plane` with `1 ↦ u`, `I ↦ v`. -/
private noncomputable def spanMap (u v : Plane) : Plane →ₗ[ℝ] Plane where
  toFun z := z.re • u + z.im • v
  map_add' z w := by
    simp only [Complex.add_re, Complex.add_im, add_smul]
    abel
  map_smul' t z := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]

@[simp] private theorem spanMap_apply (u v z : Plane) : spanMap u v z = z.re • u + z.im • v := rfl

private theorem spanMap_one (u v : Plane) : spanMap u v 1 = u := by simp

private theorem spanMap_I (u v : Plane) : spanMap u v I = v := by simp

private theorem det_spanMap (u v : Plane) : LinearMap.det (spanMap u v) = cross u v := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    spanMap_apply, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, one_smul, zero_smul,
    add_zero, zero_add]
  ring

/-- The affine translation `z ↦ a + z` as an affine map. -/
private noncomputable def addConst (a : Plane) : Plane →ᵃ[ℝ] Plane where
  toFun z := a + z
  linear := LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.id_coe, id_eq]
    ring

@[simp] private theorem addConst_apply (a z : Plane) : addConst a z = a + z := rfl

/-! ### The area of a triangle -/

/-- The area of a (possibly degenerate) triangle: the volume of
`convexHull ℝ {a, b, c}` is `|cross (b - a) (c - a)| / 2`. -/
theorem volume_triangle (a b c : Plane) :
    volume (convexHull ℝ ({a, b, c} : Set Plane))
      = ENNReal.ofReal (|cross (b - a) (c - a)| / 2) := by
  -- translate so that `a` becomes the origin
  have himg : (fun z : Plane => a + z) '' convexHull ℝ ({0, b - a, c - a} : Set Plane)
      = convexHull ℝ ({a, b, c} : Set Plane) := by
    have h := (addConst a).image_convexHull ({0, b - a, c - a} : Set Plane)
    rw [show ⇑(addConst a) = fun z : Plane => a + z from rfl] at h
    rw [h]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [show a + 0 = a from add_zero a, show a + (b - a) = b by ring,
      show a + (c - a) = c by ring]
  -- realize the translated triangle as a linear image of the standard triangle
  have h2 : convexHull ℝ ({0, b - a, c - a} : Set Plane)
      = ⇑(spanMap (b - a) (c - a)) '' stdTriangle := by
    rw [← stdTriangle_eq_hull, LinearMap.image_convexHull]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [map_zero, spanMap_one, spanMap_I]
  rw [← himg, volume_image_add, h2, Measure.addHaar_image_linearMap, det_spanMap,
    volume_stdTriangle, ← ENNReal.ofReal_mul (abs_nonneg _), mul_one_div]

/-- Any triangle with vertices in a convex set bounds its volume from below. -/
theorem triangle_area_le_volume {K : Set Plane} (hK : Convex ℝ K) {a b c : Plane}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    ENNReal.ofReal (|cross (b - a) (c - a)| / 2) ≤ volume K := by
  rw [← volume_triangle]
  refine measure_mono (convexHull_min ?_ hK)
  rintro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

/-- The shoelace value of a list of points in `Plane` (half the cyclic sum of the
cross products of consecutive points). -/
noncomputable def shoelace (l : List Plane) : ℝ :=
  (∑ i ∈ Finset.range l.length, cross (l.getD i 0) (l.getD ((i + 1) % l.length) 0)) / 2

/-- Fan expansion of the cyclic shoelace sum from the base point `w 0`. -/
theorem cyclic_fan (w : ℕ → Plane) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 3), cross (w i) (w ((i + 1) % (m + 3)))
      = ∑ j ∈ Finset.range (m + 1), cross (w (j + 1) - w 0) (w (j + 2) - w 0) := by
  have h0 : ∑ i ∈ Finset.range (m + 3), cross (w i) (w ((i + 1) % (m + 3)))
      = (∑ i ∈ Finset.range (m + 2), cross (w i) (w ((i + 1) % (m + 3))))
        + cross (w (m + 2)) (w 0) := by
    have h := Finset.sum_range_succ (fun i => cross (w i) (w ((i + 1) % (m + 3)))) (m + 2)
    rwa [show (m + 2 + 1) % (m + 3) = 0 from by
      rw [show m + 2 + 1 = m + 3 from rfl, Nat.mod_self]] at h
  have h1 : ∑ i ∈ Finset.range (m + 2), cross (w i) (w ((i + 1) % (m + 3)))
      = ∑ i ∈ Finset.range (m + 2), cross (w i) (w (i + 1)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Nat.mod_eq_of_lt (show i + 1 < m + 3 by
        have := Finset.mem_range.mp hi; omega)]
  have h2 : ∑ i ∈ Finset.range (m + 2), cross (w i) (w (i + 1))
      = (∑ i ∈ Finset.range (m + 1), cross (w (i + 1)) (w (i + 2))) + cross (w 0) (w 1) :=
    Finset.sum_range_succ' (fun i => cross (w i) (w (i + 1))) (m + 1)
  have tel : ∑ j ∈ Finset.range (m + 1), (cross (w 0) (w (j + 1)) - cross (w 0) (w (j + 2)))
      = cross (w 0) (w 1) - cross (w 0) (w (m + 2)) :=
    Finset.sum_range_sub' (fun i => cross (w 0) (w (i + 1))) (m + 1)
  have expand : ∀ j : ℕ, cross (w (j + 1) - w 0) (w (j + 2) - w 0)
      = cross (w (j + 1)) (w (j + 2))
        + (cross (w 0) (w (j + 1)) - cross (w 0) (w (j + 2))) := by
    intro j
    simp only [cross_apply, Complex.sub_re, Complex.sub_im]
    ring
  calc ∑ i ∈ Finset.range (m + 3), cross (w i) (w ((i + 1) % (m + 3)))
      = (∑ i ∈ Finset.range (m + 1), cross (w (i + 1)) (w (i + 2)))
        + cross (w 0) (w 1) + cross (w (m + 2)) (w 0) := by
        rw [h0, h1, h2]
    _ = ∑ j ∈ Finset.range (m + 1), cross (w (j + 1) - w 0) (w (j + 2) - w 0) := by
        rw [Finset.sum_congr rfl fun j _ => expand j, Finset.sum_add_distrib, tel]
        simp only [cross_apply]
        ring

/-- The shoelace expression is the sum of signed areas in the fan from the first vertex. -/
theorem shoelace_eq_fan (l : List Plane) (h3 : 3 ≤ l.length) :
    shoelace l = ∑ j ∈ Finset.range (l.length - 2),
      cross (l.getD (j + 1) 0 - l.getD 0 0)
        (l.getD (j + 2) 0 - l.getD 0 0) / 2 := by
  obtain ⟨m, hm⟩ : ∃ m, l.length = m + 3 := ⟨l.length - 3, by omega⟩
  unfold shoelace
  rw [hm, cyclic_fan, show m + 3 - 2 = m + 1 by omega, Finset.sum_div]

theorem shoelace_triangle (a b c : Plane) :
    shoelace [a, b, c] = cross (b - a) (c - a) / 2 := by
  rw [shoelace_eq_fan _ (by norm_num)]
  norm_num [Finset.sum_range_succ, List.getD]

/-- The signed identity holds for every four points, regardless of their ordering. -/
theorem shoelace_quad (a b c d : Plane) :
    shoelace [a, b, c, d] = cross (c - a) (d - b) / 2 := by
  rw [shoelace_eq_fan _ (by norm_num)]
  norm_num [Finset.sum_range_succ, List.getD, cross]
  ring

end MoserWorm
