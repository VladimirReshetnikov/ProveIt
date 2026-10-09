import GowersSzemeredi.Proofs16FreimanFrequencyTranslation

/-! Three small frequency domains contain the fourth domain of a
Freiman-respected additive quadruple, with an explicit factor of three. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem freiman_frequency_bohr_complete {N ell : Nat} [NeZero N]
    (B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    {r : Real} {a b c d w : ZMod N}
    (hrel : ∀ i, theta i a+theta i b = theta i c+theta i d)
    (ha : w ∈ freimanFrequencyBohr B theta (r/3) a)
    (hb : w ∈ freimanFrequencyBohr B theta (r/3) b)
    (hc : w ∈ freimanFrequencyBohr B theta (r/3) c) :
    w ∈ freimanFrequencyBohr B theta r d := by
  have hp := (Finset.mem_filter.mp ha).2
  have hq := (Finset.mem_filter.mp hb).2
  have ht := (Finset.mem_filter.mp hc).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have h := hp v (Finset.mem_union_left _ hv)
    have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
    nlinarith
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    have h₁ := hp (theta i a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have h₂ := hq (theta i b) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have h₃ := ht (theta i c) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have he : theta i d*w = theta i a*w+theta i b*w-theta i c*w-0 := by
      have h := hrel i
      linear_combination -w*h
    rw [he]
    have h := centeredAbs_four_term_le (theta i a*w) (theta i b*w) (theta i c*w) (0 : ZMod N)
    have hz : centeredAbs (0 : ZMod N) = 0 := by simp [centeredAbs]
    rw [hz,Nat.cast_zero,add_zero] at h
    linarith

end LeanProofs.GowersSzemeredi
