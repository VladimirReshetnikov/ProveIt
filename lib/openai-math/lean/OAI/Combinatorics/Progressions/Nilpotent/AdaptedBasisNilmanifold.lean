import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def adaptedLayerBasis (j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer j))) ℚ (F.layer j) := by
  classical
  let c := supportedSubmoduleBasis b (F.layer j) {i | j ≤ w i} (hlayers j)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem adaptedLayerBasis_height (j : ℕ) (i : Fin (finrank ℚ (F.layer j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.adaptedLayerBasis b w hlayers j i) k) 1 := by
  classical
  unfold adaptedLayerBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ k

noncomputable def ofAdaptedBasis (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d where
  filtration := F
  basis := b
  layerBasis i := F.adaptedLayerBasis b w hlayers (i.val + 1)
  lattice := Γ
  grid := N
  grid_pos := hN
  inner_grid := hin
  outer_grid := hout

theorem ofAdaptedBasis_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  refine ⟨hd, hNp, hc, ?_⟩
  intro i j k
  exact rationalLogHeight_le_of_height (F.adaptedLayerBasis_height b w hlayers _ j k)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

end Erdos3.NilpotentLieFiltration

end

end OAI
