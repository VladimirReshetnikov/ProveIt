import OAI.Combinatorics.Progressions.Linear.MultidegreeBasisConstruction
import OAI.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (e : Basis (Fin d) ℚ L)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))
  {H : ℕ} (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H)
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.ordinary
  basis := e
  layerBasis i := (F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose
  lattice := coordinateGridBCHSubgroup e B F.ordinary.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedIntegralStructure :
    (F.boundedIntegralModel e b hb B hB hstable).MultidegreeStructure bound where
  filtration := F
  ordinary := rfl
  basis a := b (fun i => (a i).val)

theorem boundedIntegralModel_basis : (F.boundedIntegralModel e b hb B hB hstable).basis = e := rfl

theorem boundedIntegralStructure_filtration :
    (F.boundedIntegralStructure e b hb B hB hstable).filtration = F := rfl

theorem boundedIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedIntegralModel e b hb B hB hstable).basis
      (F.boundedIntegralModel e b hb B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.ordinary.lowerCentralSeries_eq_bot hstable

theorem boundedIntegralStructure_complexity {p : ℝ} (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p) (hheight : (H : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    (F.boundedIntegralStructure e b hb B hB hstable).ComplexityLE p := by
  refine ⟨⟨hd, hgrid, ?_, ?_⟩, ?_⟩
  · exact fun i j k => rationalLogHeight_le_of_height (hc i j k) hheight
  · intro i j k
    exact rationalLogHeight_le_of_height
      ((F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose_spec j k) hheight
  · intro a i j
    exact rationalLogHeight_le_of_height (hb (fun k => (a k).val) i j) hheight

omit B hB hstable in
include b hb in
theorem exists_bounded_integral_model
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ M : D.MultidegreeStructure bound,
        M.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → M.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.ordinary.lowerCentralSeries_eq_bot l hl hc
  refine ⟨B, hB, hdiv, ?_, F.boundedIntegralModel e b hb B hB hstable,
    F.boundedIntegralStructure e b hb B hB hstable, rfl, rfl, rfl,
    F.boundedIntegralModel_coordinates e b hb B hB hstable, ?_⟩
  · simpa only [Fintype.card_fin] using hbound
  · intro p hd hgrid hheight
    exact F.boundedIntegralStructure_complexity e b hb B hB hstable hd hgrid hheight hc

end Erdos3.MultidegreeLieFiltration

end

end OAI
