import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_supported_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (f : Y → ℝ) (hf : ∀ y ∉ T, f y = 0) :
    (∑' x, (p x).toReal * f (F x)) = ∑ y ∈ T, (p.map F y).toReal * f y := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [pmf_image_finite_real_mean p S hp F U hU f]
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro y _ hy
  rw [hf y hy, mul_zero]

theorem pmf_pair_supported_real_mean {X Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (G : X → Z) (T : Finset Y) (U : Finset Z)
    (e : Y → ℝ) (d : Z → ℝ) (he : ∀ y ∉ T, e y = 0) (hd : ∀ z ∉ U, d z = 0) :
    (∑' x, (p x).toReal * (e (F x) * d (G x))) =
      ∑ y ∈ T, ∑ z ∈ U, (p.map (fun x => (F x, G x)) (y, z)).toReal * (e y * d z) := by
  have hoff (yz : Y × Z) (h : yz ∉ T ×ˢ U) : e yz.1 * d yz.2 = 0 := by
    by_cases hy : yz.1 ∈ T
    · have hz : yz.2 ∉ U := fun hz => h (Finset.mem_product.mpr ⟨hy, hz⟩)
      rw [hd _ hz, mul_zero]
    · rw [he _ hy, zero_mul]
  rw [pmf_image_supported_real_mean p S hp (fun x => (F x, G x)) (T ×ˢ U)
    (fun yz => e yz.1 * d yz.2) hoff, Finset.sum_product]

end Erdos3

end

end OAI
