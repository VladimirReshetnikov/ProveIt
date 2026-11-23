import GlobeFlattening.RectangularRefinement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Trimmed tiles and their area

The tiles leave a margin on both sides of every latitude core, including
the outermost rows. The union is closed and the discarded area is bounded
by seven times the relative margin.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GlobeFlattening.RectangularMesh

noncomputable section

variable (g : RectangularMesh)

/-- The closed region on which a stage agrees with one affine row formula. -/
def affineTile (i j : ℕ) : Set (ℝ × ℝ) :=
  Icc (g.longitude i) (g.longitude i + (g.width - g.margin)) ×ˢ
    Icc (g.latitude j + g.margin) (g.latitude (j + 1) - g.margin)

/-- Trimmed rectangles have a full additional margin inside each affine tile. -/
def trimmedTile (i j : ℕ) : Set (ℝ × ℝ) :=
  Icc (g.longitude i + g.margin) (g.longitude i + (g.width - 2 * g.margin)) ×ˢ
    Icc (g.latitude j + 2 * g.margin) (g.latitude j + (g.width - 2 * g.margin))

def trimmedTiles : Set (ℝ × ℝ) :=
  ⋃ a : Fin g.columns × Fin (g.transitions + 1), g.trimmedTile a.1 a.2

/-- Every point within the trimming margin of a trimmed point is still in
the same affine tile. -/
theorem mem_affineTile_of_dist {i j : ℕ} {p q : ℝ × ℝ}
    (hp : p ∈ g.trimmedTile i j) (hdist : dist q p ≤ g.margin) :
    q ∈ g.affineTile i j := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at hdist
  have hx := abs_le.mp hdist.1
  have hy := abs_le.mp hdist.2
  have hx₁ : g.longitude i + g.margin ≤ p.1 := hp.1.1
  have hx₂ : p.1 ≤ g.longitude i + (g.width - 2 * g.margin) := hp.1.2
  have hy₁ : g.latitude j + 2 * g.margin ≤ p.2 := hp.2.1
  have hy₂ : p.2 ≤ g.latitude j + (g.width - 2 * g.margin) := hp.2.2
  show (g.longitude i ≤ q.1 ∧ q.1 ≤ g.longitude i + (g.width - g.margin)) ∧
    (g.latitude j + g.margin ≤ q.2 ∧ q.2 ≤ g.latitude (j + 1) - g.margin)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith [g.latitude_succ j]⟩⟩

theorem midlatitude_close_of_mem_affineTile {i j : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ g.affineTile i j) : |p.2 - g.midlatitude j| ≤ g.width := by
  have hy₁ : g.latitude j + g.margin ≤ p.2 := hp.2.1
  have hy₂ : p.2 ≤ g.latitude (j + 1) - g.margin := hp.2.2
  unfold midlatitude
  exact abs_le.mpr ⟨by linarith [g.width_pos, g.margin_pos],
    by linarith [g.latitude_succ j, g.width_pos, g.margin_pos]⟩

theorem isClosed_trimmedTile (i j : ℕ) : IsClosed (g.trimmedTile i j) :=
  isClosed_Icc.prod isClosed_Icc

theorem isClosed_trimmedTiles : IsClosed g.trimmedTiles :=
  isClosed_iUnion_of_finite fun a => g.isClosed_trimmedTile a.1 a.2

theorem trimmedTile_subset {i j : ℕ} (hi : i < g.columns) (hj : j ≤ g.transitions) :
    g.trimmedTile i j ⊆ g.rectangle := by
  intro p hp
  have hloX := (g.longitude_mem hi.le).1
  have hhiX := g.longitude_mono (Nat.succ_le_of_lt hi)
  have hloY := g.latitude_mono (Nat.zero_le j)
  have hz : g.latitude 0 = g.bottom := by simp [latitude, meshPoint]
  rw [hz] at hloY
  have hhiY := g.latitude_mono (Nat.succ_le_succ hj)
  have hx₁ := hp.1.1
  have hx₂ := hp.1.2
  have hy₁ := hp.2.1
  have hy₂ := hp.2.2
  change g.longitude i + g.margin ≤ p.1 at hx₁
  change p.1 ≤ g.longitude i + (g.width - 2 * g.margin) at hx₂
  change g.latitude j + 2 * g.margin ≤ p.2 at hy₁
  change p.2 ≤ g.latitude j + (g.width - 2 * g.margin) at hy₂
  exact ⟨⟨by linarith [g.margin_pos], by linarith [g.longitude_succ i, g.margin_pos]⟩,
    ⟨by linarith [g.margin_pos], by linarith [g.latitude_succ j, g.margin_pos]⟩⟩

theorem trimmedTiles_subset : g.trimmedTiles ⊆ g.rectangle := by
  intro p hp
  obtain ⟨⟨i, j⟩, h⟩ := Set.mem_iUnion.mp hp
  exact g.trimmedTile_subset i.isLt (by have := j.isLt; omega) h

/-- Near a trimmed point, the stage is affine in longitude, with the
same row slope throughout the whole neighborhood. -/
theorem exists_affine_near_trimmed {u : ℝ × ℝ → ℝ} {target : ℝ → ℝ} {p : ℝ × ℝ}
    (hlip : ∀ y z : ℝ, |target y - target z| ≤ |y - z|)
    (hp : p ∈ g.trimmedTiles) :
    ∃ intercept slope : ℝ, ∀ q, dist q p ≤ g.margin →
      g.refineStage u target q = intercept + slope * q.1 ∧
      target q.2 ≤ slope ∧ slope ≤ target q.2 + 2 * g.width := by
  obtain ⟨⟨i, j⟩, htile⟩ := Set.mem_iUnion.mp hp
  have hj : (j : ℕ) ≤ g.transitions := by have := j.isLt; omega
  let slope := g.rowSlope target j
  refine ⟨u (g.longitude i, g.midlatitude j) - slope * g.longitude i, slope, ?_⟩
  intro q hdist
  have hcore := g.mem_affineTile_of_dist htile hdist
  have hval := g.refineStage_on_core (old := u) (target := target)
    i.isLt hj hcore.1.1 hcore.1.2 hcore.2.1 hcore.2.2
  refine ⟨?_, g.rowSlope_bounds hlip (g.midlatitude_close_of_mem_affineTile hcore)⟩
  rw [show q = (q.1, q.2) from (Prod.eta q).symm, hval]
  dsimp [slope]
  ring

private theorem pairwise_mesh_intervals {count : ℕ} (left width lower upper : ℝ)
    (hwidth : 0 ≤ width) (hgap : upper < width + lower) :
    (univ : Set (Fin count)).PairwiseDisjoint
      (fun i => Icc (meshPoint left width i + lower) (meshPoint left width i + upper)) := by
  rw [Set.PairwiseDisjoint, pairwise_univ, pairwise_iff_lt]
  intro i j hij
  refine disjoint_left.mpr fun x hx hy => ?_
  have hstep := meshPoint_mono (left := left) hwidth (show (i : ℕ) + 1 ≤ j from hij)
  rw [meshPoint_succ] at hstep
  linarith [hx.2, hy.1]

theorem pairwise_trimmedTile :
    Pairwise (Function.onFun Disjoint (fun a : Fin g.columns × Fin (g.transitions + 1) =>
      g.trimmedTile a.1 a.2)) := by
  have hx := pairwise_mesh_intervals (count := g.columns) g.left g.width
    g.margin (g.width - 2 * g.margin) g.width_pos.le (by linarith [g.margin_pos])
  have hy := pairwise_mesh_intervals (count := g.transitions + 1) g.bottom g.width
    (2 * g.margin) (g.width - 2 * g.margin) g.width_pos.le (by linarith [g.margin_pos])
  simpa only [univ_prod_univ, Set.PairwiseDisjoint, pairwise_univ, trimmedTile, longitude, latitude] using hx.prod hy

theorem volume_rectangle :
    volume g.rectangle =
      ENNReal.ofReal ((g.columns : ℝ) * (g.transitions + 1 : ℕ) * g.width ^ 2) := by
  unfold rectangle longitude latitude meshPoint
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  simp only [add_sub_cancel_left]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) g.width_pos.le)]
  congr 1
  ring

theorem volume_trimmedTile (hmargin : 4 * g.margin ≤ g.width) (i j : ℕ) :
    volume (g.trimmedTile i j) =
      ENNReal.ofReal ((g.width - 3 * g.margin) * (g.width - 4 * g.margin)) := by
  have hx : g.longitude i + (g.width - 2 * g.margin) -
      (g.longitude i + g.margin) = g.width - 3 * g.margin := by ring
  have hy : g.latitude j + (g.width - 2 * g.margin) -
      (g.latitude j + 2 * g.margin) = g.width - 4 * g.margin := by ring
  rw [trimmedTile, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    hx, hy, ← ENNReal.ofReal_mul (by linarith [g.margin_pos])]

theorem volume_trimmedTiles (hmargin : 4 * g.margin ≤ g.width) :
    volume g.trimmedTiles = ENNReal.ofReal
      ((g.columns : ℝ) * (g.transitions + 1 : ℕ) *
        ((g.width - 3 * g.margin) * (g.width - 4 * g.margin))) := by
  rw [trimmedTiles, measure_iUnion g.pairwise_trimmedTile
    (fun a => (g.isClosed_trimmedTile a.1 a.2).measurableSet), tsum_fintype]
  simp only [g.volume_trimmedTile hmargin, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- The exact rectangular count gives the report's bound for the discarded
area. This uniform estimate also accounts for cells along the boundary. -/
theorem volume_discarded (hmargin : 4 * g.margin ≤ g.width) :
    volume (g.rectangle \ g.trimmedTiles) ≤ ENNReal.ofReal
      (7 * (g.margin / g.width) * ((g.columns : ℝ) * (g.transitions + 1 : ℕ) * g.width ^ 2)) := by
  have hvol : volume g.trimmedTiles ≠ ∞ := by
    rw [g.volume_trimmedTiles hmargin]
    exact ENNReal.ofReal_ne_top
  have hcard : 0 ≤ (g.columns : ℝ) * (g.transitions + 1 : ℕ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤
      (g.columns : ℝ) * (g.transitions + 1 : ℕ) *
        ((g.width - 3 * g.margin) * (g.width - 4 * g.margin)) :=
    mul_nonneg hcard (mul_nonneg (by linarith [g.margin_pos]) (by linarith))
  rw [measure_sdiff g.trimmedTiles_subset g.isClosed_trimmedTiles.measurableSet.nullMeasurableSet hvol,
    g.volume_rectangle, g.volume_trimmedTiles hmargin, ← ENNReal.ofReal_sub _ hnonneg]
  apply ENNReal.ofReal_le_ofReal
  have hbound : g.width ^ 2 - (g.width - 3 * g.margin) * (g.width - 4 * g.margin) ≤
      7 * g.margin * g.width := by nlinarith [sq_nonneg g.margin]
  calc
    _ = ((g.columns : ℝ) * (g.transitions + 1 : ℕ)) *
      (g.width ^ 2 - (g.width - 3 * g.margin) * (g.width - 4 * g.margin)) := by ring
    _ ≤ ((g.columns : ℝ) * (g.transitions + 1 : ℕ)) * (7 * g.margin * g.width) :=
      mul_le_mul_of_nonneg_left hbound hcard
    _ = _ := by field_simp [g.width_pos.ne']

end

end GlobeFlattening.RectangularMesh
