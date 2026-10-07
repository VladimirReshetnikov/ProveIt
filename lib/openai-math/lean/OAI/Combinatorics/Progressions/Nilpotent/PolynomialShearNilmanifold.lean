/- Modified for ProveIt: rewrite the supported-submodule basis at default
transparency on Lean 4.32. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit

namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearLayerBasis (r : ℕ) :
    Basis {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  supportedSubmoduleBasis (polynomialShearOrderedBasis w) (polynomialShearLayer w r)
    {j | r ≤ polynomialShearOrderedWeight w j} (polynomialShearOrderedBasis_layers w r)

theorem polynomialShearLayerBasis_height (r : ℕ)
    (i : {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}) (j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerBasis w r i).val j) 1 := by
  rw [polynomialShearLayerBasis]
  erw [supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (polynomialShearOrderedBasis w) _ _

noncomputable def polynomialShearLayerIndexEquiv (r : ℕ) :
    {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j} ≃
      Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (polynomialShearLayerBasis w r)).symm

noncomputable def polynomialShearLayerFinBasis (r : ℕ) :
    Basis (Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)))
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  (polynomialShearLayerBasis w r).reindex (polynomialShearLayerIndexEquiv w r)

theorem polynomialShearLayerFinBasis_height (r : ℕ) (i j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerFinBasis w r i).val j) 1 := by
  rw [polynomialShearLayerFinBasis, Basis.reindex_apply]
  exact polynomialShearLayerBasis_height w r _ _

noncomputable def polynomialShearNilmanifold (s : ℕ) (hw : ∀ i, w i ≤ s) :
    RationalFilteredNilmanifold (PolynomialShearLieAlgebra w ℚ) s
      (Fintype.card (PolynomialShearIndex w)) where
  filtration := polynomialShearFiltration w s hw
  basis := polynomialShearOrderedBasis w
  layerBasis i := polynomialShearLayerFinBasis w (i.val + 1)
  lattice := polynomialShearLattice w s hw
  grid := s.factorial
  grid_pos := Nat.factorial_pos s
  inner_grid := polynomialShearOrderedBasis_inner_grid w s hw
  outer_grid := polynomialShearOrderedBasis_outer_grid w s hw

theorem polynomialShearNilmanifold_complexity (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ p)
    (hf : (s.factorial : ℝ) ≤ Real.exp p)
    (hH : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp p) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE p := by
  refine ⟨hd, hf, ?_, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearOrderedBasis_structure_height w s hpos hw i j k) hH
  · intro i j k
    exact rationalLogHeight_le_of_height (polynomialShearLayerFinBasis_height w (i.val + 1) j k)
      (by simpa using Real.one_le_exp_iff.mpr hp)

theorem polynomialShearNilmanifold_complexity_budget (s : ℕ) (hpos : ∀ i, 0 < w i)
    (hw : ∀ i, w i ≤ s) :
    (polynomialShearNilmanifold w s hw).GeometryComplexityLE
      ((Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1 : ℕ) : ℝ) := by
  let n := Fintype.card (PolynomialShearIndex w) + s.factorial + 2 * s + 1
  have hn : (Fintype.card (PolynomialShearIndex w) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show Fintype.card (PolynomialShearIndex w) ≤ n by dsimp [n]; omega)
  have hf : (s.factorial : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show s.factorial ≤ n by dsimp [n]; omega)
  have hH : ((2 * s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * s + 1 ≤ n by dsimp [n]; omega)
  have he : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  exact polynomialShearNilmanifold_complexity w s hpos hw (Nat.cast_nonneg n) hn
    (hf.trans he) (hH.trans he)

end Erdos3

end

end OAI
