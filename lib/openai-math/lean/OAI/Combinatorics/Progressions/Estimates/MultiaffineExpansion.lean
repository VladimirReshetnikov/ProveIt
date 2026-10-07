import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def multiaffineExpansion {R : Type*} [CommRing R] {n : ℕ}
    (c : Finset (Fin n) → R) (x : Fin n → R) : R :=
  ∑ S : Finset (Fin n), c S * ∏ i, if i ∈ S then x i else 1

theorem multiaffineExpansion_box_difference {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (c : Finset (Fin n) → Z → R)
    (f : ∀ i, X i → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n
      (fun x t => multiaffineExpansion (fun S => c S t) (fun i => f i (x i))) u v z =
      c Finset.univ z * ∏ i, (f i (u i)-f i (v i)) := by
  unfold multiaffineExpansion
  rw [additiveBoxDifference_sum]
  have hprod (S : Finset (Fin n)) :
      additiveBoxDifference n (fun x t => c S t * ∏ i, if i ∈ S then f i (x i) else 1) u v z =
        c S z * ∏ i, ((if i ∈ S then f i (u i) else 1)-(if i ∈ S then f i (v i) else 1)) :=
    additiveBoxDifference_product n (c S) (fun i x => if i ∈ S then f i x else 1) u v z
  simp_rw [hprod]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · simp
  · intro S _ hS
    have hmissing : ∃ i, i ∉ S := by
      by_contra h
      apply hS
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hmissing
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · exact mul_zero _
    · simp only [hi, ite_false, sub_self]
  · simp

end Erdos3

end

end OAI
