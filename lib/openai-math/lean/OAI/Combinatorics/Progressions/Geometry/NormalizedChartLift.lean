import OAI.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_eq_of_sub_mem (u : W) (x : W × (Fin n → ℤ))
    (hx : u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D) :
    QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  let v : W := x.1 - projectedLatticeShift (standardEuclideanLattice D) W z
  have hv : QuotientAddGroup.mk'
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup v =
        normalizedLatticeQuotient W b hb x := rfl
  have hdiff := normalizedLatticePoint_sub_mem_of_mk_eq W b hb v x hv
  have hm : (u - v).val ∈ standardEuclideanLattice D := by
    convert (standardEuclideanLattice D).sub_mem hx hdiff using 1
    simp only [Submodule.coe_sub]
    abel
  exact (QuotientAddGroup.eq_iff_sub_mem.mpr hm).trans hv

theorem exists_normalized_chart_lift (u : W) (v : EuclideanSpace ℝ D)
    (hv : u.val - v ∈ standardEuclideanLattice D) :
    ∃ x : W × (Fin n → ℤ), normalizedLatticePoint W b x = v ∧
      normalizedLatticeQuotient W b hb x =
        QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
  have hproj : Wᗮ.orthogonalProjectionOnto v ∈ span ℤ (Set.range b) := by
    rw [hb]
    apply (projectedIntegerLattice W).neg_mem_iff.mp
    change -(Wᗮ.orthogonalProjectionOnto v) ∈
      (standardEuclideanLattice D).map (Wᗮ.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)
    refine ⟨u.val - v, hv, ?_⟩
    change Wᗮ.orthogonalProjectionOnto (u.val - v) = -Wᗮ.orthogonalProjectionOnto v
    rw [map_sub, Wᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr (by simp), zero_sub]
  obtain ⟨z, hz⟩ := normalizedOrthogonalChart_integer_coordinates W b v hproj
  let x : W × (Fin n → ℤ) := ((normalizedOrthogonalChart W b v).1, z)
  have hx : normalizedLatticePoint W b x = v := by
    apply (normalizedOrthogonalChart W b).injective
    change (normalizedOrthogonalChart W b) ((normalizedOrthogonalChart W b).symm
      ((normalizedOrthogonalChart W b v).1, fun i => (z i : ℝ) / basisAxisScale b i)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (funext (fun i => (hz i).symm))
  refine ⟨x, hx, (normalizedLatticeQuotient_eq_of_sub_mem W b hb u x ?_).symm⟩
  rwa [hx]

end Erdos3

end

end OAI
