import OAI.Combinatorics.Progressions.Estimates.RealOrderedSlots
import OAI.Combinatorics.Progressions.Lattices.ChartLatticePeriodization

namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Λ : Subgroup (NilpotentLieBCHGroup L s hnil))
  [MetricSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
    (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom)]

include he

theorem realOrderedSlots_patchValue (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (z g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (phi : OpenPartialHomeomorph (Fin d → ℝ)
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
        (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom))
    (hphi : ∀ v, phi v = QuotientGroup.mk
      (z * (⟨(e.baseChange ℝ).equivFun.symm v⟩ : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
        (realification_lowerCentralSeries_eq_bot hnil))))
    (F : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom) → ℝ)
    (hF : Function.support F ⊆ phi.target) (Phi : PatchKernel d)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi F ((B : ℝ) • v)) :
    (realOrderedSlots (e.baseChange ℝ) (realification_lowerCentralSeries_eq_bot hnil)
      (B : ℝ) (z⁻¹ * g)).patchValue Phi = F (QuotientGroup.mk g) := by
  let q : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ≃
      (Fin d → ℝ) :=
    { toFun := fun a => (e.baseChange ℝ).equivFun a.coord
      invFun := fun v => ⟨(e.baseChange ℝ).equivFun.symm v⟩
      left_inv := fun a => NilpotentLieBCHGroup.ext
        ((e.baseChange ℝ).equivFun.symm_apply_apply a.coord)
      right_inv := fun v => (e.baseChange ℝ).equivFun.apply_symm_apply v }
  apply triangular_patchValue_eq_chartObservable (Λ.map realificationHom)
    q (realIntegralOrderedBasisProduct e hnil B)
    (realIntegralOrderedBasisProduct_mem e hnil Λ B hgrid)
    (he.exists_realIntegralOrderedBasisProduct hnil Λ B hgrid) z g phi hphi F hF
    _ Phi (B : ℝ) hPhi
  intro b
  exact he.real_baseChange.smul_realOrderedSlots_residual
    (realification_lowerCentralSeries_eq_bot hnil) (B : ℝ)
    (by exact_mod_cast hB.ne') (z⁻¹ * g) b

end Erdos3.IsCentralLieBasis

end

end OAI
