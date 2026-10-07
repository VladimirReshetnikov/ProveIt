import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_triple_fibers {G : Type*} (A : Finset G) (P : A → Finset (G × G)) :
    ∃ Q : Finset (G × G × G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  classical
  let e : (Σ _ : A, G × G) ↪ G × G × G := {
    toFun := fun t => (t.1.val, t.2)
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrArg Prod.fst h)
      have huv : u = v := congrArg Prod.snd h
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have ha := (Finset.mem_sigma.mp hau).2
      exact ⟨a, congrArg Prod.fst heq, (congrArg Prod.snd heq) ▸ ha⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, t.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      exact Prod.ext ha rfl

theorem dense_triple_fibers {G : Type*} [Fintype G]
    (A : Finset G) (P : A → Finset (G × G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ 2 ≤ (P a).card) :
    ∃ Q : Finset (G × G × G),
      α * β * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_triple_fibers A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ 2) := by ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (sq_nonneg _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI
