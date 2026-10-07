import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem graded_top_kernel_iff_refiltered_top_kernel
    {ι L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ a ∈ U, basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0) ↔
    (∀ x ∈ F.gradedRefiltrationLayer U s, φ x = 0 → x = 0) := by
  constructor
  · exact fun htop => F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop
  · intro htop a ha hpure hzero
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s a hpure
    have hxU : (x : L) ∈ F.gradedRefiltrationLayer U s := by
      apply (F.mem_gradedRefiltrationLayer U s x).mpr
      exact ⟨x.property, hx.symm ▸ ha⟩
    have hpiece : G.associatedGradedPieceMap s ⟨φ x, hφ s x x.property⟩ = 0 := by
      rw [← F.associatedGradedMap_piece G φ hφ s x, hx]
      exact hzero
    have hφzero : φ x = 0 := by
      have hmem := (G.associatedGradedPieceMap_eq_zero_iff s
        ⟨φ x, hφ s x x.property⟩).mp hpiece
      rw [G.terminal] at hmem
      exact hmem
    have hxzero : x = 0 := Subtype.ext (htop x hxU hφzero)
    rw [← hx, hxzero, map_zero]

theorem joinedFrequency_graded_refiltered_top_kernel
    {ι L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
    (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
    (eta : J → L →ₗ[ℚ] ℚ) (js : List J) (partner : J → W →ₗ[ℚ] ℚ)
    (H : NilpotentLieFiltration ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) s)
    (G : NilpotentLieFiltration (Y × W) s)
    (e : Basis ι ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)) (ω : ι → ℕ)
    (hH : ∀ j, H.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (hφ : ∀ j, ∀ x ∈ H.layer j, F.pivotProductMarkedMap π eta js x ∈ G.layer j)
    (U : LieSubalgebra ℚ H.AssociatedGraded)
    (hjoined : H.gradedRefiltrationLayer U s ≤ F.joinedFrequencyQuotientTop π eta js partner) :
    ∀ a ∈ U, basisGradeProjection (H.associatedGradedBasis e ω hH) ω s a = a →
      H.associatedGradedMap G (F.pivotProductMarkedMap π eta js) hφ a = 0 → a = 0 := by
  apply (H.graded_top_kernel_iff_refiltered_top_kernel G e ω hH
    (F.pivotProductMarkedMap π eta js) hφ U).mpr
  intro x hx hzero
  exact F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js partner x (hjoined hx) hzero

end Erdos3.NilpotentLieFiltration

end

end OAI
