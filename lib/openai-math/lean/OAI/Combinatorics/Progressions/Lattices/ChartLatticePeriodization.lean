import Mathlib.GroupTheory.Coset.Basic
import OAI.Combinatorics.Progressions.Linear.NativeChartKernel

namespace OAI

section

namespace Erdos3

theorem triangular_patchValue_eq_chartObservable {G : Type*} [Group G] {d : ℕ}
    (Λ : Subgroup G) [MetricSpace (G ⧸ Λ)] (q : G ≃ (Fin d → ℝ))
    (gamma : (Fin d → ℤ) → G) (hgamma : ∀ b, gamma b ∈ Λ)
    (hsurj : ∀ a ∈ Λ, ∃ b, gamma b = a) (z g : G)
    (phi : OpenPartialHomeomorph (Fin d → ℝ) (G ⧸ Λ))
    (hphi : ∀ v, phi v = QuotientGroup.mk (z * q.symm v))
    (F : (G ⧸ Λ) → ℝ) (hF : Function.support F ⊆ phi.target)
    (A : TriangularSlots d) (Phi : PatchKernel d) (B : ℝ)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi F (B • v))
    (hA : ∀ b, B • A.residual b = q (z⁻¹ * g * gamma b)) :
    A.patchValue Phi = F (QuotientGroup.mk g) := by
  have hchart (b : Fin d → ℤ) : phi (B • A.residual b) = QuotientGroup.mk g := by
    rw [hphi, hA, q.symm_apply_apply]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem g (hgamma b)
  by_cases hzero : F (QuotientGroup.mk g) = 0
  · rw [hzero]
    apply A.patchValue_eq_zero
    intro b
    rw [hPhi]
    by_cases hb : B • A.residual b ∈ phi.source
    · rw [chartCoordinateKernel_of_mem phi F hb, hchart b, hzero]
    · exact chartCoordinateKernel_of_not_mem phi F hb
  · have hx : QuotientGroup.mk g ∈ phi.target := hF hzero
    let v := phi.symm (QuotientGroup.mk g)
    have hv : v ∈ phi.source := phi.map_target hx
    have heq : (QuotientGroup.mk (z * q.symm v) : G ⧸ Λ) = QuotientGroup.mk g :=
      (hphi v).symm.trans (phi.right_inv hx)
    have hmem : g⁻¹ * (z * q.symm v) ∈ Λ := QuotientGroup.eq.mp heq.symm
    obtain ⟨b, hb⟩ := hsurj _ hmem
    have hcoord : B • A.residual b = v := by
      rw [hA, hb]
      have hcancel : z⁻¹ * g * (g⁻¹ * (z * q.symm v)) = q.symm v := by group
      rw [hcancel, q.apply_symm_apply]
    have hvalue : Phi.value (A.residual b) = F (QuotientGroup.mk g) := by
      rw [hPhi, hcoord, chartCoordinateKernel_of_mem phi F hv, phi.right_inv hx]
    have hnz : Phi.value (A.residual b) ≠ 0 := by rwa [hvalue]
    exact (A.patchValue_eq_of_nonzero Phi hnz).trans hvalue

end Erdos3

end

end OAI
