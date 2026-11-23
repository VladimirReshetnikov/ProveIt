import GlobeFlattening.LatitudeProfile

/-!
# Locating cells and interpolation layers of the rectangular mesh
-/

open Set

namespace GlobeFlattening

noncomputable section

/-- The closed cells of a finite mesh cover its closed interval. -/
theorem exists_mesh_cell {left width x : ℝ} {count : ℕ} (hcount : 0 < count)
    (hx₁ : left ≤ x) (hx₂ : x ≤ meshPoint left width count) :
    ∃ j < count, meshPoint left width j ≤ x ∧ x ≤ meshPoint left width (j + 1) := by
  have hlast : count - 1 + 1 = count := by omega
  have hlast' : x ≤ meshPoint left width ((count - 1) + 1) := by simpa only [hlast] using hx₂
  have hex : ∃ j, x ≤ meshPoint left width (j + 1) := ⟨count - 1, hlast'⟩
  have hfind := Nat.find_min' hex hlast'
  refine ⟨Nat.find hex, by omega, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
  · have hpoint : meshPoint left width (Nat.find hex) = left := by
      rw [hzero]
      simp [meshPoint]
    exact hpoint.le.trans hx₁
  · have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hnot := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [heq] at hnot
    exact (lt_of_not_ge hnot).le

/-- One square grid on a closed rectangle. The vertical parameter counts
interior latitude grid lines, so there is one more row than that parameter. -/
structure RectangularMesh where
  left : ℝ
  bottom : ℝ
  width : ℝ
  margin : ℝ
  columns : ℕ
  transitions : ℕ
  columns_pos : 0 < columns
  margin_pos : 0 < margin
  layer_small : 2 * margin < width

namespace RectangularMesh

def longitude (g : RectangularMesh) : ℕ → ℝ := meshPoint g.left g.width

def latitude (g : RectangularMesh) : ℕ → ℝ := meshPoint g.bottom g.width

def midlatitude (g : RectangularMesh) (j : ℕ) : ℝ := g.latitude j + g.width / 2

def layerStart (g : RectangularMesh) (j : ℕ) : ℝ := g.latitude (j + 1) - g.margin

def rectangle (g : RectangularMesh) : Set (ℝ × ℝ) :=
  Icc g.left (g.longitude g.columns) ×ˢ Icc g.bottom (g.latitude (g.transitions + 1))

theorem width_pos (g : RectangularMesh) : 0 < g.width := by
  linarith [g.layer_small, g.margin_pos]

theorem latitude_succ (g : RectangularMesh) (j : ℕ) :
    g.latitude (j + 1) = g.latitude j + g.width :=
  meshPoint_succ _ _ _

theorem longitude_succ (g : RectangularMesh) (j : ℕ) :
    g.longitude (j + 1) = g.longitude j + g.width :=
  meshPoint_succ _ _ _

theorem latitude_mono (g : RectangularMesh) : Monotone g.latitude :=
  meshPoint_mono g.width_pos.le

theorem longitude_mono (g : RectangularMesh) : Monotone g.longitude :=
  meshPoint_mono g.width_pos.le

theorem longitude_mem (g : RectangularMesh) {j : ℕ} (hj : j ≤ g.columns) :
    g.longitude j ∈ Icc g.left (g.longitude g.columns) := by
  have hlo := g.longitude_mono (Nat.zero_le j)
  have hz : g.longitude 0 = g.left := by simp [longitude, meshPoint]
  exact ⟨hz.ge.trans hlo, g.longitude_mono hj⟩

theorem margin_lt_width (g : RectangularMesh) : g.margin < g.width := by
  linarith [g.layer_small, g.margin_pos]

theorem midlatitude_mem (g : RectangularMesh) {j : ℕ} (hj : j ≤ g.transitions) :
    g.midlatitude j ∈ Icc g.bottom (g.latitude (g.transitions + 1)) := by
  have h₀ := g.latitude_mono (Nat.zero_le j)
  have h₁ := g.latitude_mono (Nat.succ_le_succ hj)
  have hstep := g.latitude_succ j
  have hz : g.latitude 0 = g.bottom := by simp [latitude, meshPoint]
  rw [hz] at h₀
  constructor <;> unfold midlatitude <;> linarith [g.width_pos]

private theorem midlatitude_close (g : RectangularMesh) {y : ℝ} {j : ℕ}
    (h₁ : g.latitude j - g.margin ≤ y) (h₂ : y ≤ g.latitude (j + 1) + g.margin) :
    |y - g.midlatitude j| ≤ g.width := by
  have hstep := g.latitude_succ j
  unfold midlatitude
  exact abs_le.mpr ⟨by linarith [g.layer_small], by linarith [g.layer_small]⟩

theorem interpolate_at_core (g : RectangularMesh) (row : ℕ → ℝ → ℝ)
    {j : ℕ} {y x : ℝ} (hj : j ≤ g.transitions)
    (hy₁ : g.latitude j + g.margin ≤ y) (hy₂ : y ≤ g.latitude (j + 1) - g.margin) :
    latitudeProfile g.layerStart (2 * g.margin) g.transitions row (x, y) = row j x := by
  apply latitudeProfile_at_core (by linarith [g.margin_pos]) hj
  · intro i hi
    have hgrid := g.latitude_mono (show i + 1 ≤ j by omega)
    unfold layerStart
    dsimp
    linarith
  · intro i _ hi
    have hgrid := g.latitude_mono (show j + 1 ≤ i + 1 by omega)
    unfold layerStart
    dsimp
    linarith

private theorem layer_blend (g : RectangularMesh) (row : ℕ → ℝ → ℝ)
    {j : ℕ} {y : ℝ} (hj : j < g.transitions)
    (hy₁ : g.latitude (j + 1) - g.margin ≤ y)
    (hy₂ : y ≤ g.latitude (j + 1) + g.margin) :
    ∀ x, latitudeProfile g.layerStart (2 * g.margin) g.transitions row (x, y) =
      (1 - latitudeWeight (g.layerStart j) (2 * g.margin) y) * row j x +
        latitudeWeight (g.layerStart j) (2 * g.margin) y * row (j + 1) x := by
  intro x
  apply latitudeProfile_at_layer (by linarith [g.margin_pos]) hj
  · intro i hi
    have hgrid := g.latitude_mono (show i + 1 ≤ j by omega)
    have hstep := g.latitude_succ j
    unfold layerStart
    dsimp
    linarith [g.layer_small]
  · intro i _ hi
    have hgrid := g.latitude_mono (show j + 1 + 1 ≤ i + 1 by omega)
    have hstep := g.latitude_succ (j + 1)
    unfold layerStart
    dsimp
    linarith [g.layer_small]

/-- At any latitude in the closed rectangle the interpolation is a convex
combination of rows whose midpoints are within one mesh width. The row
indices and weights work for every longitude on that latitude. -/
theorem exists_latitude_blend (g : RectangularMesh) (row : ℕ → ℝ → ℝ) {y : ℝ}
    (hy : y ∈ Icc g.bottom (g.latitude (g.transitions + 1))) :
    ∃ i j : ℕ, ∃ t : ℝ, i ≤ g.transitions ∧ j ≤ g.transitions ∧ 0 ≤ t ∧ t ≤ 1 ∧
      |y - g.midlatitude i| ≤ g.width ∧ |y - g.midlatitude j| ≤ g.width ∧
      ∀ x, latitudeProfile g.layerStart (2 * g.margin) g.transitions row (x, y) =
        (1 - t) * row i x + t * row j x := by
  obtain ⟨j, hj, hyleft, hyright⟩ :=
    exists_mesh_cell (width := g.width) (count := g.transitions + 1) (by omega) hy.1 hy.2
  change g.latitude j ≤ y at hyleft
  change y ≤ g.latitude (j + 1) at hyright
  have hleft_margin : g.latitude j - g.margin ≤ y := by linarith [g.margin_pos]
  have hright_margin : y ≤ g.latitude (j + 1) + g.margin := by linarith [g.margin_pos]
  by_cases hl : 0 < j ∧ y < g.latitude j + g.margin
  · let i := j - 1
    have hij : i + 1 = j := by dsimp [i]; omega
    have hi : i < g.transitions := by omega
    let t := latitudeWeight (g.layerStart i) (2 * g.margin) y
    have ht : 0 ≤ t ∧ t ≤ 1 := latitudeWeight_bounds (by linarith [g.margin_pos])
    have hprev : g.latitude i ≤ g.latitude j := g.latitude_mono (by omega)
    refine ⟨i, j, t, by omega, by omega, ht.1, ht.2, ?_, ?_, ?_⟩
    · exact g.midlatitude_close (by linarith) (by rw [hij]; exact hl.2.le)
    · exact g.midlatitude_close hleft_margin hright_margin
    · have h := g.layer_blend row (y := y) hi (by simpa only [hij] using hleft_margin)
        (by simpa only [hij] using hl.2.le)
      simpa only [hij, t] using h
  by_cases hr : j < g.transitions ∧ g.latitude (j + 1) - g.margin < y
  · let t := latitudeWeight (g.layerStart j) (2 * g.margin) y
    have ht : 0 ≤ t ∧ t ≤ 1 := latitudeWeight_bounds (by linarith [g.margin_pos])
    have hnext : g.latitude (j + 1) ≤ g.latitude (j + 1 + 1) :=
      g.latitude_mono (Nat.le_succ _)
    refine ⟨j, j + 1, t, by omega, by omega, ht.1, ht.2,
      g.midlatitude_close hleft_margin hright_margin, g.midlatitude_close hr.2.le ?_, ?_⟩
    · linarith
    · exact g.layer_blend row hr.1 hr.2.le hright_margin
  have hmid := g.midlatitude_close hleft_margin hright_margin
  refine ⟨j, j, 0, by omega, by omega, le_rfl, zero_le_one, hmid, hmid, ?_⟩
  intro x
  have heq : latitudeProfile g.layerStart (2 * g.margin) g.transitions row (x, y) =
      row j x := by
    apply latitudeProfile_at_core (by linarith [g.margin_pos]) (by omega : j ≤ g.transitions)
    · intro i hi
      have hgrid := g.latitude_mono (show i + 1 ≤ j by omega)
      have hmargin : g.latitude j + g.margin ≤ y :=
        le_of_not_gt fun h => hl ⟨by omega, h⟩
      unfold layerStart
      dsimp
      linarith
    · intro i hi hji
      have hgrid := g.latitude_mono (show j + 1 ≤ i + 1 by omega)
      have hmargin : y ≤ g.latitude (j + 1) - g.margin :=
        le_of_not_gt fun h => hr ⟨by omega, h⟩
      unfold layerStart
      dsimp
      linarith
  simpa using heq

end RectangularMesh

end

end GlobeFlattening
