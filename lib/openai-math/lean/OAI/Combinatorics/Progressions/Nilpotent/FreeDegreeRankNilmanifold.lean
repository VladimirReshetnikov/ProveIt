import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
import OAI.Combinatorics.Progressions.Sampling.ControlledIntegralGrid

namespace OAI

section

namespace Erdos3

theorem scaledIntegerGrid_le_denominatorGrid {ι : Type*} (a b : ℕ) :
    (scaledIntegerGrid a : Set (ι → ℚ)) ⊆ denominatorGrid b := by
  rintro x ⟨z, rfl⟩
  exact ((show IntegralVector (fun i => (z i : ℚ)) from ⟨z, fun _ => rfl⟩).nat_smul a).nat_smul b

namespace DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L)
  (htail : ∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c)

noncomputable def tailLayerBasis (i j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer i j))) ℚ (F.layer i j) :=
  basisOfTail b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2

theorem tailLayerBasis_height (i j : ℕ) (a : Fin (finrank ℚ (F.layer i j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.tailLayerBasis b htail i j a : L) k) 1 :=
  basisOfTail_height b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2 a k

variable (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule b B, ∀ y ∈ coordinateGridModule b B,
    lieBCH s x y ∈ coordinateGridModule b B)

noncomputable def integralGridNilmanifold : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := b
  layerBasis i := F.tailLayerBasis b htail (i.val + 1) 0
  lattice := coordinateGridBCHSubgroup b B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def integralGridDegreeRank :
    (F.integralGridNilmanifold b htail B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis i j := F.tailLayerBasis b htail i.val j.val

theorem integralGridNilmanifold_basis : (F.integralGridNilmanifold b htail B hB hstable).basis = b := rfl

theorem integralGridDegreeRank_filtration :
    (F.integralGridDegreeRank b htail B hB hstable).filtration = F := rfl

theorem integralGridNilmanifold_coordinates :
    bchSubgroupCoordinates (F.integralGridNilmanifold b htail B hB hstable).basis
      (F.integralGridNilmanifold b htail B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates b B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem integralGridDegreeRank_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.integralGridDegreeRank b htail B hB hstable).ComplexityLE p := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp p := by
    simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp
  refine ⟨⟨hd, hgrid, hc, ?_⟩, ?_⟩
  · intro i a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail (i.val + 1) 0 a k) hone
  · intro i j a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail i.val j.val a k) hone

end DegreeRankLieFiltration

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_controlled_nilmanifold_of_tails (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L : Type*) [LieRing L] [LieAlgebra ℚ L] (r d : ℕ)
      (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L),
      (∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c) →
      ∀ (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ D : RationalFilteredNilmanifold L s d,
        ∃ R : D.DegreeRankStructure r, D.basis = b ∧ R.filtration = F ∧
          l ∣ D.grid ∧ bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨C, hC, hgrid⟩ := exists_controlled_integral_grid s
  refine ⟨C, hC, ?_⟩
  intro L _ _ r d F b htail l hl p hp hd hlp hc
  obtain ⟨hpC, B, hB, hdiv, hBbound, hstable⟩ := hgrid L (Fin d) b
    F.associatedDegree.lowerCentralSeries_eq_bot l hl p hp
    (by simpa only [Fintype.card_fin] using hd) hlp hc
  refine ⟨hpC, F.integralGridNilmanifold b htail B hB hstable,
    F.integralGridDegreeRank b htail B hB hstable, rfl, rfl, hdiv,
    F.integralGridNilmanifold_coordinates b htail B hB hstable, ?_⟩
  exact F.integralGridDegreeRank_complexity b htail B hB hstable
    (hp.trans hpC) (hd.trans hpC) hBbound (fun i j k => (hc i j k).trans hpC)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_free_degree_rank_nilmanifold (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (l : ℕ), 0 < l →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p → (l : ℝ) ≤ Real.exp p →
      ∃ D : RationalFilteredNilmanifold (FreeDegreeRankLieAlgebra X s r w hw) s
          (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw)),
        ∃ R : D.DegreeRankStructure r,
          R.filtration = FreeDegreeRankLieAlgebra.filtration X s r w hw hr ∧
          R.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis D.basis ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
            rationalLogHeight (D.basis.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
          ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
            (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
            (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
            ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
                (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
              LinearMap.toMatrix e D.basis (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
              ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hfree⟩ := exists_adapted_free_degree_rank_model s
  obtain ⟨c, _, hnative⟩ := exists_controlled_nilmanifold_of_tails s
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw l hl p hp hX hlp
  let B := (p + a) ^ a
  let T := p + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBT : B ≤ T := le_add_of_nonneg_left hp
  have hpT : p ≤ T := le_add_of_nonneg_right hB
  have hT : 0 ≤ T := hp.trans hpT
  have hsum : T + (T + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, T, B, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + c) ^ c)).trans hsum
  have hNC : (T + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hdim, b, hcentral, htail, hstructure, htree, e, he, hdim₀, S, hS, hSH⟩ :=
    hfree X r hr w hw p hp hX
  obtain ⟨_, D, R, hb, hR, hdiv, hcoords, hcomplexity⟩ :=
    hnative (FreeDegreeRankLieAlgebra X s r w hw) r _
      (FreeDegreeRankLieAlgebra.filtration X s r w hw hr) b htail l hl T hT
      (hdim.trans hBT) (hlp.trans (Real.exp_le_exp.mpr hpT))
      (fun i j k => (hstructure i j k).trans hBT)
  refine ⟨D, R, hR, hcomplexity.mono R hNC, ?_, hdiv, hcoords, ?_, e, he,
    hdim₀.trans (hBT.trans hTC), S, ?_, fun i j => (hSH i j).trans (hBT.trans hTC)⟩
  · rw [hb]
    exact hcentral
  · intro x hx i
    rw [hb]
    exact (htree x hx i).trans (hBT.trans hTC)
  · rw [hb]
    exact hS

end Erdos3

end

end OAI
