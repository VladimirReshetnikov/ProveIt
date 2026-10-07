import Mathlib

namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem exists_dense_translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A P : Finset G) (hA : A.Nonempty) {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q)
    (hbound : ((A - P).card : ℝ) ≤ q) (hsize : δ * q ≤ (P.card : ℝ)) :
    ∃ t ∈ A - P, ∃ F ⊆ A, F.Nonempty ∧ δ * A.card ≤ (F.card : ℝ) ∧
      ∀ a ∈ F, a - t ∈ P := by
  classical
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hPpos : (0 : ℝ) < P.card := (mul_pos hδ hq).trans_le hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpos)
  have hD : (A - P).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨p, hp⟩ := hP
    exact ⟨a - p, Finset.mem_sub.mpr ⟨a, ha, p, hp, rfl⟩⟩
  have hcount : (A - P).card • (δ * (A.card : ℝ)) ≤ ((A ×ˢ P).card : ℝ) := by
    rw [nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ q * (δ * A.card) := mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = (A.card : ℝ) * (δ * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg A.card)
  obtain ⟨t, ht, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := A ×ˢ P) (t := A - P) (f := fun x => x.1 - x.2)
    (fun x hx => Finset.mem_sub.mpr
      ⟨x.1, (Finset.mem_product.mp hx).1, x.2, (Finset.mem_product.mp hx).2, rfl⟩)
    hD hcount
  let T := (A ×ˢ P).filter fun x => x.1 - x.2 = t
  let F := T.image Prod.fst
  have hinj : Set.InjOn (Prod.fst : G × G → G) (T : Set (G × G)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    apply Prod.ext hxy
    have h := hx'.trans hy'.symm
    rw [hxy] at h
    exact sub_right_inj.mp h
  have hcard : F.card = T.card := Finset.card_image_of_injOn hinj
  have hFlarge : δ * A.card ≤ (F.card : ℝ) := by rw [hcard]; exact hlarge
  have hFpos : (0 : ℝ) < F.card := (mul_pos hδ hApos).trans_le hFlarge
  refine ⟨t, ht, F, ?_, Finset.card_pos.mp (by exact_mod_cast hFpos), hFlarge, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
    have hx' := Finset.mem_filter.mp hx
    have heq : a - t = x.2 := by rw [← hxa, ← hx'.2]; abel
    rw [heq]
    exact (Finset.mem_product.mp hx'.1).2

end Erdos3

end

end OAI
