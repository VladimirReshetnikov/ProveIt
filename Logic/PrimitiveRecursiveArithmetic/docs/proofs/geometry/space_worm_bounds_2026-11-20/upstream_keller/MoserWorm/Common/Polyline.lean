/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Data.List.GetD
import MoserWorm.Common.Defs

/-!
# Polyline arcs

`polyline vs` is the piecewise-linear path through the vertices `vs` with
uniform parameter spacing on `[0, 1]`.  We use the closed form
`v 0 + ∑ k, clamp₀₁ (t * m - k) • (v (k + 1) - v k)` (where `m = vs.length - 1`,
`v k = vs.getD k 0` and `clamp₀₁ x = max 0 (min 1 x)`), which is manifestly
continuous and agrees with `AffineMap.lineMap (v k) (v (k + 1))` (suitably
reparametrized) on each subinterval `[k/m, (k+1)/m]`.

Main results: the arc length (total variation on `[0, 1]`) of a polyline is
the sum of the distances between consecutive vertices, and arc length, unit
arcs and arc images transform as expected under plane isometries.
-/

open Set AffineMap

namespace MoserWorm

/-! ### Polylines -/

/-- The piecewise-linear path through the vertices `vs`, with uniform parameter
spacing on `[0, 1]`.  With `m = vs.length - 1` and `v k = vs.getD k 0`, on
`[k/m, (k+1)/m]` it interpolates linearly from `v k` to `v (k + 1)`
(see `MoserWorm.polyline_eqOn`); it is constantly `v 0` on `(-∞, 0]` and constantly
`v m` on `[1, ∞)`. -/
noncomputable def polyline (vs : List ℂ) (t : ℝ) : ℂ :=
  vs.getD 0 0 + ∑ k ∈ Finset.range (vs.length - 1),
    max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) • (vs.getD (k + 1) 0 - vs.getD k 0)

/-- A polyline is continuous (on all of `ℝ`). -/
theorem polyline_continuous (vs : List ℂ) : Continuous (polyline vs) := by
  unfold polyline
  refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
  exact (continuous_const.max (continuous_const.min
    ((continuous_mul_const _).sub continuous_const))).smul continuous_const

/-- A polyline is continuous on `[0, 1]`. -/
theorem polyline_continuousOn (vs : List ℂ) (_h : 2 ≤ vs.length) :
    ContinuousOn (polyline vs) (Icc 0 1) :=
  (polyline_continuous vs).continuousOn

/-- On the `i`-th subinterval `[i/m, (i+1)/m]` (with `m = vs.length - 1`), the
polyline is the affine interpolation from vertex `i` to vertex `i + 1`. -/
theorem polyline_eqOn (vs : List ℂ) {i : ℕ} (hi : i < vs.length - 1) :
    EqOn (polyline vs)
      (⇑(lineMap (vs.getD i 0) (vs.getD (i + 1) 0) : ℝ →ᵃ[ℝ] ℂ) ∘
        fun t : ℝ => t * ((vs.length - 1 : ℕ) : ℝ) - (i : ℝ))
      (Icc ((i : ℝ) / ((vs.length - 1 : ℕ) : ℝ))
        (((i + 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ))) := by
  intro t ht
  have hm : 0 < vs.length - 1 := lt_of_le_of_lt (Nat.zero_le i) hi
  have hmR : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by exact_mod_cast hm
  obtain ⟨ht0, ht1⟩ := ht
  rw [div_le_iff₀ hmR] at ht0
  rw [le_div_iff₀ hmR] at ht1
  push_cast at ht1
  -- `ht0 : (i : ℝ) ≤ t * m`, `ht1 : t * m ≤ (i : ℝ) + 1`
  have hones : (∑ k ∈ Finset.range i,
      max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) •
        (vs.getD (k + 1) 0 - vs.getD k 0)) = vs.getD i 0 - vs.getD 0 0 :=
    calc
      (∑ k ∈ Finset.range i,
          max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) •
            (vs.getD (k + 1) 0 - vs.getD k 0))
        = ∑ k ∈ Finset.range i, (vs.getD (k + 1) 0 - vs.getD k 0) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hk' : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hk
          rw [min_eq_left (by linarith), max_eq_right zero_le_one, one_smul]
      _ = vs.getD i 0 - vs.getD 0 0 := Finset.sum_range_sub (fun k => vs.getD k 0) i
  have hzeros : (∑ k ∈ Finset.Ico (i + 1) (vs.length - 1),
      max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) •
        (vs.getD (k + 1) 0 - vs.getD k 0)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    have hx : t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ) ≤ 0 := by linarith
    rw [min_eq_right (hx.trans zero_le_one), max_eq_left hx, zero_smul]
  have e0 : (0 : ℝ) ≤ t * ((vs.length - 1 : ℕ) : ℝ) - (i : ℝ) := by linarith
  have e1 : t * ((vs.length - 1 : ℕ) : ℝ) - (i : ℝ) ≤ 1 := by linarith
  simp only [polyline, Function.comp_apply, lineMap_apply_module']
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hi), Finset.sum_range_succ,
    hones, hzeros, min_eq_right e1, max_eq_right e0]
  module

/-- The total variation of an affine segment `lineMap p q` over the unit
interval is the distance between its endpoints. -/
theorem eVariationOn_lineMap (p q : ℂ) :
    eVariationOn (⇑(lineMap p q : ℝ →ᵃ[ℝ] ℂ)) (Icc (0 : ℝ) 1) = edist p q := by
  refine le_antisymm ?_ ?_
  · -- Upper bound: `lineMap p q` is `dist p q`-Lipschitz and `id` has variation `1`.
    have h := ((lipschitzWith_lineMap (𝕜 := ℝ) p q).lipschitzOnWith
      (s := univ)).comp_eVariationOn_le (mapsTo_univ id (Icc (0 : ℝ) 1))
    simp only [Function.comp_id, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one,
      mul_one] at h
    rwa [edist_nndist]
  · -- Lower bound: the chain `0, 1` already has total distance `edist p q`.
    have h := eVariationOn.edist_le (⇑(lineMap p q : ℝ →ᵃ[ℝ] ℂ))
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    simpa using h

/-- The variation of a polyline over the `i`-th subinterval is the length of
its `i`-th edge. -/
theorem eVariationOn_polyline_segment (vs : List ℂ) {i : ℕ} (hi : i < vs.length - 1) :
    eVariationOn (polyline vs)
      (Icc ((i : ℝ) / ((vs.length - 1 : ℕ) : ℝ))
        (((i + 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ))) =
      edist (vs.getD i 0) (vs.getD (i + 1) 0) := by
  have hm : 0 < vs.length - 1 := lt_of_le_of_lt (Nat.zero_le i) hi
  have hmR : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have hφ : MonotoneOn (fun t : ℝ => t * ((vs.length - 1 : ℕ) : ℝ) - (i : ℝ))
      (Icc ((i : ℝ) / ((vs.length - 1 : ℕ) : ℝ))
        (((i + 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ))) := by
    intro a _ b _ hab
    have := mul_le_mul_of_nonneg_right hab hmR.le
    dsimp only
    linarith
  have himg : (fun t : ℝ => t * ((vs.length - 1 : ℕ) : ℝ) - (i : ℝ)) ''
      Icc ((i : ℝ) / ((vs.length - 1 : ℕ) : ℝ))
        (((i + 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ)) = Icc (0 : ℝ) 1 := by
    ext y
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      rw [div_le_iff₀ hmR] at h1
      rw [le_div_iff₀ hmR] at h2
      push_cast at h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨(y + (i : ℝ)) / ((vs.length - 1 : ℕ) : ℝ), ⟨?_, ?_⟩, ?_⟩
      · rw [div_le_div_iff_of_pos_right hmR]
        linarith
      · rw [div_le_div_iff_of_pos_right hmR]
        push_cast
        linarith
      · rw [div_mul_cancel₀ _ hmR.ne']
        ring
  rw [eVariationOn.congr (polyline_eqOn vs hi),
    eVariationOn.comp_eq_of_monotoneOn _ _ hφ, himg]
  exact eVariationOn_lineMap _ _

/-- The arc length of a polyline is the sum of the distances between
consecutive vertices. -/
theorem arcLength_polyline (vs : List ℂ) (h : 2 ≤ vs.length) :
    arcLength (polyline vs) =
      ∑ k ∈ Finset.range (vs.length - 1), edist (vs.getD k 0) (vs.getD (k + 1) 0) := by
  have hm : 0 < vs.length - 1 := by omega
  have hmR : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have hI : Monotone fun i : ℕ => (i : ℝ) / ((vs.length - 1 : ℕ) : ℝ) := by
    intro a b hab
    rw [div_le_div_iff_of_pos_right hmR]
    exact_mod_cast hab
  have key := eVariationOn.sum' (polyline vs) hI (n := vs.length - 1)
  simp only [Nat.cast_zero, zero_div, div_self hmR.ne'] at key
  unfold arcLength
  rw [← key]
  exact Finset.sum_congr rfl fun i hi =>
    eVariationOn_polyline_segment vs (Finset.mem_range.1 hi)

/-! ### Arcs and isometries -/

/-- Total variation is invariant under post-composition by an isometry. -/
theorem eVariationOn_isometry_comp (g : ℂ ≃ᵢ ℂ) (f : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (⇑g ∘ f) s = eVariationOn f s := by
  simp only [eVariationOn, Function.comp_apply, g.isometry.edist_eq]

/-- Arc length is invariant under post-composition by a plane isometry. -/
theorem arcLength_isometry_comp (g : ℂ ≃ᵢ ℂ) (f : ℝ → ℂ) :
    arcLength (⇑g ∘ f) = arcLength f :=
  eVariationOn_isometry_comp g f _

/-- An isometric copy of a unit arc is a unit arc. -/
theorem isUnitArc_isometry (g : ℂ ≃ᵢ ℂ) (f : ℝ → ℂ) (hf : IsUnitArc f) :
    IsUnitArc (⇑g ∘ f) :=
  ⟨g.continuous.comp_continuousOn hf.1, (arcLength_isometry_comp g f).trans hf.2⟩

/-- The image of an isometric copy of an arc is the isometric copy of its image. -/
theorem trace_isometry_comp (g : ℂ ≃ᵢ ℂ) (f : ℝ → ℂ) :
    trace (⇑g ∘ f) = g '' trace f := by
  simp only [trace, Set.image_comp]

theorem polyline_map_add (vs : List ℂ) (h : 0 < vs.length) (c : ℂ) (t : ℝ) :
    polyline (vs.map (fun z => z + c)) t = polyline vs t + c := by
  have hget : ∀ k : ℕ, k < vs.length →
      (vs.map (fun z => z + c)).getD k 0 = vs.getD k 0 + c := by
    intro k hk
    rw [List.getD_eq_getElem _ 0 (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ 0 hk]
  unfold polyline
  simp only [List.length_map]
  rw [hget 0 h]
  have hs :
      (∑ k ∈ Finset.range (vs.length - 1),
        max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) •
          ((vs.map (fun z => z + c)).getD (k + 1) 0 -
            (vs.map (fun z => z + c)).getD k 0)) =
      ∑ k ∈ Finset.range (vs.length - 1),
        max 0 (min 1 (t * ((vs.length - 1 : ℕ) : ℝ) - (k : ℝ))) •
          (vs.getD (k + 1) 0 - vs.getD k 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [hget (k + 1) (by omega), hget k (by omega), add_sub_add_right_eq_sub]
  rw [hs]
  abel

theorem isUnitArc_polyline_map_add (vs : List ℂ) (h : 0 < vs.length) (c : ℂ)
    (hu : IsUnitArc (polyline vs)) :
    IsUnitArc (polyline (vs.map (fun z => z + c))) := by
  have he : polyline (vs.map (fun z => z + c)) =
      ⇑(IsometryEquiv.addRight c) ∘ polyline vs := by
    funext t
    exact polyline_map_add vs h c t
  rw [he]
  exact isUnitArc_isometry _ _ hu

/-- Every parameter lies in one of the consecutive closed parameter intervals. -/
theorem polyline_parameter_segment (m : ℕ) (hm : 0 < m) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < m ∧ t ∈ Icc ((i : ℝ) / m) (((i + 1 : ℕ) : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases h1 : t = 1
  · refine ⟨m - 1, by omega, ?_⟩
    subst t
    constructor
    · apply (div_le_iff₀ hmR).2
      norm_cast
      omega
    · have he : m - 1 + 1 = m := by omega
      simp [he, ne_of_gt hmR]
  · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
    have h0 : 0 ≤ t * m := mul_nonneg ht.1 hmR.le
    refine ⟨⌊t * m⌋₊, (Nat.floor_lt h0).2 ?_, ?_, ?_⟩
    · nlinarith
    · exact (div_le_iff₀ hmR).2 (Nat.floor_le h0)
    · apply (le_div_iff₀ hmR).2
      push_cast
      exact (Nat.lt_floor_add_one (t * m)).le

/-- A polyline is contained in the convex hull of its vertices. -/
theorem trace_polyline_subset_hull (vs : List ℂ) (h : 2 ≤ vs.length) :
    trace (polyline vs) ⊆ convexHull ℝ {z | z ∈ vs} := by
  rintro z ⟨t, ht, rfl⟩
  obtain ⟨i, hi, hit⟩ := polyline_parameter_segment (vs.length - 1) (by omega) ht
  rw [polyline_eqOn vs hi hit]
  apply (convex_convexHull ℝ _).lineMap_mem
  · apply subset_convexHull ℝ _
    rw [List.getD_eq_getElem vs 0 (by omega)]
    exact List.getElem_mem (by omega)
  · apply subset_convexHull ℝ _
    rw [List.getD_eq_getElem vs 0 (by omega)]
    exact List.getElem_mem (by omega)
  · have hm : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < vs.length - 1 by omega)
    have ha := (div_le_iff₀ hm).1 hit.1
    have hb := (le_div_iff₀ hm).1 hit.2
    push_cast at hb
    constructor <;> dsimp <;> linarith

/-- The value at a vertex parameter is the corresponding vertex. -/
theorem polyline_at_vertex (vs : List ℂ) (h : 2 ≤ vs.length)
    {i : ℕ} (hi : i < vs.length) :
    polyline vs ((i : ℝ) / ((vs.length - 1 : ℕ) : ℝ)) = vs.getD i 0 := by
  have hm : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < vs.length - 1 by omega)
  by_cases hil : i < vs.length - 1
  · rw [polyline_eqOn vs hil (left_mem_Icc.2 (by
      apply div_le_div_of_nonneg_right _ hm.le
      exact_mod_cast Nat.le_succ i))]
    simp [Function.comp_apply, div_mul_cancel₀ _ hm.ne']
  · have he : i = vs.length - 1 := by omega
    have him : i - 1 < vs.length - 1 := by omega
    have his : i - 1 + 1 = i := by omega
    have hpoint : (i : ℝ) / ((vs.length - 1 : ℕ) : ℝ) ∈
        Icc (((i - 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ))
          (((i - 1 + 1 : ℕ) : ℝ) / ((vs.length - 1 : ℕ) : ℝ)) := by
      rw [his]
      apply right_mem_Icc.2
      apply div_le_div_of_nonneg_right _ hm.le
      exact_mod_cast Nat.sub_le i 1
    rw [polyline_eqOn vs him hpoint]
    have hiR : (i : ℝ) - ((i - 1 : ℕ) : ℝ) = 1 := by
      have hs : ((i - 1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast his
      linarith
    simp [Function.comp_apply, div_mul_cancel₀ _ hm.ne', hiR, his]

/-- Every listed vertex occurs in the trace, including the final endpoint. -/
theorem vertices_subset_trace_polyline (vs : List ℂ) (h : 2 ≤ vs.length) :
    {z | z ∈ vs} ⊆ trace (polyline vs) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
  refine ⟨(i : ℝ) / ((vs.length - 1 : ℕ) : ℝ), ?_, ?_⟩
  · have hm : (0 : ℝ) < ((vs.length - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < vs.length - 1 by omega)
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hm.le
    · apply (div_le_one hm).2
      exact_mod_cast (show i ≤ vs.length - 1 by omega)
  · rw [polyline_at_vertex vs h hi, List.getD_eq_getElem vs 0 hi]

/-- Replacing a polygonal trace by its listed vertices preserves the hull. -/
theorem convexHull_trace_polyline (vs : List ℂ) (h : 2 ≤ vs.length) :
    convexHull ℝ (trace (polyline vs)) = convexHull ℝ {z | z ∈ vs} := by
  apply le_antisymm
  · exact convexHull_min (trace_polyline_subset_hull vs h) (convex_convexHull ℝ _)
  · exact convexHull_mono (vertices_subset_trace_polyline vs h)

end MoserWorm
