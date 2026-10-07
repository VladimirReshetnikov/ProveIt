import Mathlib

namespace OAI

section

namespace Erdos3

theorem finite_product_mass_bound {ι κ : Type*} [Fintype ι]
    (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) {B : ℝ}
    (hB : ∀ s : Finset κ, ∑ x ∈ s, f x ≤ B) (s : Finset (ι → κ)) :
    (∑ z ∈ s, ∏ i, f (z i)) ≤ B ^ Fintype.card ι := by
  classical
  let T := s.biUnion (fun z => Finset.univ.image z)
  have hsub : s ⊆ Fintype.piFinset (fun _ : ι => T) := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Fintype.piFinset (fun _ : ι => T), ∏ i, f (z i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => Finset.prod_nonneg fun i _ => hf (z i))
    _ = (∑ x ∈ T, f x) ^ Fintype.card ι := by
      rw [Finset.sum_prod_piFinset]
      simp only [Finset.prod_const, Finset.card_univ]
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => hf x) (hB T) _

end Erdos3

end

end OAI
