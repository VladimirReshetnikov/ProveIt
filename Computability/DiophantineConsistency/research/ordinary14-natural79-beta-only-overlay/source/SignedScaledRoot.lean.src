import DiophantineConsistency.Compact44.P72Root

/-! Source-only sign-preserving scaled square extraction, model generic.
No Lean elaboration, graph identification or sign orientation is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.SignedScaledRootDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A scaled signed square has a natural root and one of two exact signed
representations. The sign is not selected or assumed. -/
theorem scaled_signed_root (U n : V) (Z : DiffRing V) (hU : 0<U)
    (h : Z*Z=(ι U*ι U)*ι n) :
    ∃ d : V, d*d=n ∧ (Z=ι (U*d) ∨ Z= -ι (U*d)) := by
  rcases nonneg_or_nonpos Z with ⟨z,hz⟩ | ⟨z,hz⟩
  · have hsq : z*z=U*U*n := by
      apply ι_injective
      rw [hz] at h
      simpa only [map_mul] using h
    obtain ⟨d,hd,hn⟩ := scaled_quotient U z n hU hsq
    refine ⟨d,hn,Or.inl ?_⟩
    rw [hz,hd]
  · have hsq : z*z=U*U*n := by
      apply ι_injective
      rw [hz] at h
      simpa only [neg_mul_neg,map_mul] using h
    obtain ⟨d,hd,hn⟩ := scaled_quotient U z n hU hsq
    refine ⟨d,hn,Or.inr ?_⟩
    rw [hz,hd]

end DiophantineConsistency.SignedScaledRootDraft

#print axioms DiophantineConsistency.SignedScaledRootDraft.scaled_signed_root
