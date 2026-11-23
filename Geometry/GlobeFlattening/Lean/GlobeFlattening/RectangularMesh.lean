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

/-- Locate the first unfinished interpolation layer, or the last row if
all layers have finished. This gives the two contributing rows uniformly
at the boundary and in the interior. -/
theorem exists_latitude_blend (g : RectangularMesh) (row : ℕ → ℝ → ℝ) {y : ℝ}
    (hy : y ∈ Icc g.bottom (g.latitude (g.transitions + 1))) :
    ∃ i j : ℕ, ∃ t : ℝ, i ≤ g.transitions ∧ j ≤ g.transitions ∧ 0 ≤ t ∧ t ≤ 1 ∧
      |y - g.midlatitude i| ≤ g.width ∧ |y - g.midlatitude j| ≤ g.width ∧
      ∀ x, latitudeProfile g.layerStart (2 * g.margin) g.transitions row (x, y) =
        (1 - t) * row i x + t * row j x := by
  have hex : ∃ j, g.transitions ≤ j ∨ y ≤ g.latitude (j + 1) + g.margin :=
    ⟨g.transitions, Or.inl le_rfl⟩
  let j := Nat.find hex
  have hcount : j ≤ g.transitions := Nat.find_min' hex (Or.inl le_rfl)
  have hprev (i : ℕ) (hi : i < j) : g.latitude (i + 1) + g.margin ≤ y :=
    (lt_of_not_ge fun h => Nat.find_min hex hi (Or.inr h)).le
  have hbefore (i : ℕ) (hi : i < j) : g.layerStart i + 2 * g.margin ≤ y := by
    unfold layerStart
    linarith [hprev i hi]
  have hleft : g.latitude j - g.margin ≤ y := by
    rcases Nat.eq_zero_or_pos j with hz | hpos
    · rw [hz]
      simpa [latitude, meshPoint] using (sub_le_self g.bottom g.margin_pos.le).trans hy.1
    · have h := hprev (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at h
      linarith [g.margin_pos]
  have hright : y ≤ g.latitude (j + 1) + g.margin := by
    rcases Nat.find_spec hex with hlast | hright
    · have h : j = g.transitions := le_antisymm hcount hlast
      rw [h]
      linarith [hy.2, g.margin_pos]
    · exact hright
  have hmid := g.midlatitude_close hleft hright
  have hw : 0 < 2 * g.margin := by positivity [g.margin_pos]
  by_cases hj : j < g.transitions ∧ g.layerStart j ≤ y
  · let t := latitudeWeight (g.layerStart j) (2 * g.margin) y
    have ht := latitudeWeight_bounds (start := g.layerStart j) (y := y) hw
    have hmid' : |y - g.midlatitude (j + 1)| ≤ g.width :=
      g.midlatitude_close hj.2
        (hright.trans (add_le_add (g.latitude_mono (Nat.le_succ _)) le_rfl))
    refine ⟨j, j + 1, t, hcount, Nat.succ_le_of_lt hj.1, ht.1, ht.2, hmid, hmid', ?_⟩
    intro x
    apply latitudeProfile_at_layer hw hj.1 hbefore
    intro i _ hi
    have hgrid := g.latitude_mono (show j + 2 ≤ i + 1 by omega)
    unfold layerStart
    dsimp
    linarith [g.latitude_succ (j + 1), g.layer_small]
  refine ⟨j, j, 0, hcount, hcount, le_rfl, zero_le_one, hmid, hmid, ?_⟩
  intro x
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  apply latitudeProfile_at_core hw hcount hbefore
  intro i hi hji
  have hstart : y ≤ g.layerStart j := le_of_not_ge fun h => hj ⟨lt_of_le_of_lt hji hi, h⟩
  exact hstart.trans (sub_le_sub_right (g.latitude_mono (Nat.succ_le_succ hji)) _)

end RectangularMesh

end

end GlobeFlattening
