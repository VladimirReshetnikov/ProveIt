import OAI.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis (Fin d) ℚ L)
  (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
    ℚ (F.associatedDegree.layer (i.val + 1)))
  (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
    ℚ (F.layer i.val j.val))
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedRankIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := e
  layerBasis := b
  lattice := coordinateGridBCHSubgroup e B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedRankIntegralStructure :
    (F.boundedRankIntegralModel e b B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis := c

theorem boundedRankIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedRankIntegralModel e b B hB hstable).basis
      (F.boundedRankIntegralModel e b B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem boundedRankIntegralStructure_complexity {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hd : (d : ℝ) ≤ p) (hgrid : (B : ℝ) ≤ Real.exp p)
    (hheight : (H : ℝ) ≤ Real.exp p) :
    (F.boundedRankIntegralStructure e b c B hB hstable).ComplexityLE p :=
  ⟨⟨hd, hgrid, fun i j k => rationalLogHeight_le_of_height (hbracket i j k) hheight,
    fun i a j => rationalLogHeight_le_of_height (hb i a j) hheight⟩,
    fun i j a k => rationalLogHeight_le_of_height (hc i j a k) hheight⟩

omit B hB hstable in
theorem exists_bounded_rank_integral_model {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.associatedDegree.lowerCentralSeries_eq_bot l hl hbracket
  exact ⟨B, hB, hdiv, by simpa only [Fintype.card_fin] using hbound,
    F.boundedRankIntegralModel e b B hB hstable,
    F.boundedRankIntegralStructure e b c B hB hstable, rfl, rfl, rfl,
    F.boundedRankIntegralModel_coordinates e b B hB hstable,
    fun _ hd hg hh => F.boundedRankIntegralStructure_complexity e b c B hB hstable
      hb hc hbracket hd hg hh⟩

omit B hB hstable in
theorem exists_bounded_rank_integral_model_with_frequency {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (ξ : L →ₗ[ℚ] ℚ) (hξ : ∀ i, RationalHeightLE (ξ (e i)) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * (l * H ^ d) ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  classical
  let k := arrayDenominator (fun i => ξ (e i))
  have hk : 0 < k := arrayDenominator_pos _
  have hkH : k ≤ H ^ d := by
    simpa only [Fintype.card_fin] using arrayDenominator_le (fun i => ξ (e i)) (fun i => (hξ i).2)
  obtain ⟨B, hB, hdiv, hbound, D, T, hTF, hDe, hDB, hcoords, hcomplex⟩ :=
    F.exists_bounded_rank_integral_model e b c hb hc hbracket (l * k) (Nat.mul_pos hl hk)
  refine ⟨B, hB, (dvd_mul_right l k).trans hdiv,
    hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left l hkH)),
    D, T, hTF, hDe, hDB, hcoords, ?_, hcomplex⟩
  intro z hz
  have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
    rw [← hcoords]
    change (⟨D.basis.equivFun.symm (D.basis.equivFun z.coord)⟩ : D.filtration.Group) ∈ D.lattice
    simpa only [LinearEquiv.symm_apply_apply] using hz
  rw [hDe] at hgrid
  exact coordinateGrid_functional_integral e ξ k B ((dvd_mul_left k l).trans hdiv)
    (fun i => ⟨clearedArray (fun j => ξ (e j)) i, (clearedArray_cast _ i).symm⟩) hgrid

end Erdos3.DegreeRankLieFiltration

end

end OAI
