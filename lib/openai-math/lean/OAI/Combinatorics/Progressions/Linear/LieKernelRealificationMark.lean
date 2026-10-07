import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem mem_realificationLieKernel_iff (φ : L →ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    x ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ realificationLieHom φ x = 0 := by
  rw [real_baseChange_ker]
  rfl

theorem realificationLieSubalgebra_ker (φ : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra φ.ker.toLieSubalgebra =
      (realificationLieHom φ).ker.toLieSubalgebra := by
  ext x
  change x ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ realificationLieHom φ x = 0
  exact mem_realificationLieKernel_iff φ x

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem coord_mem_realificationKernel_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  rw [mem_realificationLieKernel_iff]
  constructor
  · intro h
    exact ext h
  · intro h
    exact congrArg coord h

theorem mem_realificationSubgroup_ker_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ realificationSubgroup (hnil := hnil) φ.ker.toLieSubalgebra ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  change g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ _
  exact coord_mem_realificationKernel_iff φ g

theorem realificationSubgroup_ker (φ : L →ₗ⁅ℚ⁆ M) :
    realificationSubgroup (hnil := hnil) φ.ker.toLieSubalgebra =
      (realificationMap (hnil := hnil) (hM := hM) φ).ker := by
  ext g
  exact mem_realificationSubgroup_ker_iff φ g

theorem exists_realificationKernel_lift (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (hg : realificationMap (hnil := hnil) (hM := hM) φ g = 1) :
    ∃ x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] φ.ker.toLieSubalgebra) s
        (realification_lowerCentralSeries_eq_bot
          (lie_subalgebra_lowerCentralSeries_eq_bot hnil φ.ker.toLieSubalgebra)),
      realificationMap
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil φ.ker.toLieSubalgebra)
        (hM := hnil) φ.ker.toLieSubalgebra.incl x = g := by
  have hm := (mem_realificationSubgroup_ker_iff φ g).mpr hg
  rw [← realificationMap_incl_range] at hm
  exact hm

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
