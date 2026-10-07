import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_tuple_fibers {G : Type*} (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) :
    ∃ Q : Finset (Fin (d + 1) → G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  classical
  let e : (Σ _ : A, Fin d → G) ↪ (Fin (d + 1) → G) := {
    toFun := fun t => Fin.cons t.1.val t.2
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrFun h 0)
      have huv : u = v := by funext i; exact congrFun h i.succ
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have hu := (Finset.mem_sigma.mp hau).2
      have hut : u = Fin.tail t := by funext i; exact congrFun heq i.succ
      exact ⟨a, congrFun heq 0, hut ▸ hu⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, Fin.tail t⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact ha

theorem dense_tuple_fibers {G : Type*} [Fintype G] (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ d ≤ (P a).card) :
    ∃ Q : Finset (Fin (d + 1) → G),
      α * β * (Fintype.card G : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_tuple_fibers d A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ d) := by rw [pow_succ]; ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (pow_nonneg (Nat.cast_nonneg _) _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI
