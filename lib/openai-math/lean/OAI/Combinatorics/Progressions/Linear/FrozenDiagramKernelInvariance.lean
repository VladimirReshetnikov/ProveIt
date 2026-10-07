import OAI.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realification_map_mem_of_kernel
    {H L M : Type*} [AddCommGroup H] [Module ℚ H]
    [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]
    (φ : H →ₗ[ℚ] L) (ψ : H →ₗ[ℚ] M) (K : Submodule ℚ L)
    (hker : ∀ x, ψ x = 0 → φ x ∈ K)
    (x : ℝ ⊗[ℚ] H) (hx : ψ.baseChange ℝ x = 0) :
    φ.baseChange ℝ x ∈ K.baseChange ℝ := by
  have hle : LinearMap.ker ψ ≤ K.comap φ := fun y hy => hker y hy
  have hreal := Submodule.baseChange_mono ℝ hle
  rw [realification_ker, realification_comap] at hreal
  exact hreal hx

theorem realificationLieHom_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationLieHom ψ) := by
  let _ : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) ψ.toLinearMap hψ

namespace NilpotentLieBCHGroup

theorem realificationMap_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hH : LieModule.lowerCentralSeries ℚ H H s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationMap (hnil := hH) (hM := hM) ψ) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_injective ψ hψ
  exact congrArg coord hxy

end NilpotentLieBCHGroup

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup

theorem frozenDiagramKernelInvariance_of_injective
    {H L M : Type*} [LieRing H] [LieAlgebra ℚ H]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d e f : ℕ}
    (D : RationalFilteredNilmanifold H s d)
    (E : RationalFilteredNilmanifold L t e)
    (T : RationalFilteredNilmanifold M r f)
    (φ : H →ₗ⁅ℚ⁆ L) (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ)
    (u : E.Space → ℂ) (a b : E.RealGroup) :
    ∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * b)) =
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * b)) := by
  intro z hz x
  have hz1 : z = 1 := realificationMap_injective ψ hψ
    ((MonoidHom.mem_ker.mp hz).trans (map_one _).symm)
  rw [hz1, one_mul]

end RationalFilteredNilmanifold

end Erdos3

end

end OAI
