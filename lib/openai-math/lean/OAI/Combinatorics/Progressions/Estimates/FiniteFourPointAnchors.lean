import Mathlib

namespace OAI

section

namespace Erdos3

theorem exists_dense_pair_slice {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (T : Finset (A × B)) {δ : ℝ} (hδ : 0 < δ)
    (hsize : δ * Fintype.card A * Fintype.card B ≤ (T.card : ℝ)) :
    ∃ (a : A) (S : Finset B), S.Nonempty ∧
      δ * Fintype.card B ≤ (S.card : ℝ) ∧ ∀ b ∈ S, (a, b) ∈ T := by
  classical
  have hcount : Fintype.card A • (δ * Fintype.card B) ≤ (Fintype.card T : ℝ) := by
    simpa only [nsmul_eq_mul, Fintype.card_coe, mul_left_comm, mul_assoc] using hsize
  obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card (fun t : T => t.val.1) hcount
  let F := Finset.univ.filter (fun t : T => t.val.1 = a)
  let e : F ↪ B := {
    toFun := fun t => t.val.val.2
    inj' := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext ((Finset.mem_filter.mp u.property).2.trans
        (Finset.mem_filter.mp v.property).2.symm) huv }
  let S := Finset.univ.map e
  have hS : δ * Fintype.card B ≤ (S.card : ℝ) := by
    simpa only [S, Finset.card_map, Finset.card_univ, Fintype.card_coe] using ha
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < S.card := (mul_pos hδ hB).trans_le hS
  refine ⟨a, S, Finset.card_pos.mp (by exact_mod_cast hpos), hS, ?_⟩
  intro b hb
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hb
  change (a, t.val.val.2) ∈ T
  rw [← (Finset.mem_filter.mp t.property).2]
  exact t.val.property

end Erdos3

end

section

namespace Erdos3

variable (G : Type*) [AddCommGroup G]

def fourSparse12Equiv : (G × G × G) ≃ (G × G) × G where
  toFun t := ((t.2.2, t.2.1), t.2.1 - t.1)
  invFun u := (u.1.2 - u.2, u.1.2, u.1.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; simp

def fourSparse13Equiv : (G × G × G) ≃ (G × G) × G where
  toFun t := ((t.2.2, t.2.2 - t.1), t.2.1 - t.1)
  invFun u := (u.1.1 - u.1.2, u.2 + (u.1.1 - u.1.2), u.1.1)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; simp

variable {G} [Fintype G]

theorem exists_dense_four_sparse12_slice (T : Finset (G × G × G)) {δ : ℝ}
    (hδ : 0 < δ) (hsize : δ * (Fintype.card G : ℝ) ^ 3 ≤ T.card) :
    ∃ (a b : G) (S : Finset G), S.Nonempty ∧
      δ * Fintype.card G ≤ (S.card : ℝ) ∧ ∀ h ∈ S, (b - h, b, a) ∈ T := by
  classical
  let e := fourSparse12Equiv G
  have hnew : δ * Fintype.card (G × G) * Fintype.card G ≤
      ((T.map e.toEmbedding).card : ℝ) := by
    rw [Finset.card_map, Fintype.card_prod, Nat.cast_mul]
    convert hsize using 1
    ring
  obtain ⟨⟨a, b⟩, S, hS, hSsize, hmem⟩ := exists_dense_pair_slice (T.map e.toEmbedding) hδ hnew
  refine ⟨a, b, S, hS, hSsize, ?_⟩
  intro h hh
  obtain ⟨t, ht, he⟩ := Finset.mem_map.mp (hmem h hh)
  have hinv : e.symm ((a, b), h) = t := by
    rw [← he]
    exact e.symm_apply_apply t
  change e.symm ((a, b), h) ∈ T
  rwa [hinv]

theorem exists_dense_four_sparse13_slice (T : Finset (G × G × G)) {δ : ℝ}
    (hδ : 0 < δ) (hsize : δ * (Fintype.card G : ℝ) ^ 3 ≤ T.card) :
    ∃ (a b : G) (S : Finset G), S.Nonempty ∧
      δ * Fintype.card G ≤ (S.card : ℝ) ∧ ∀ h ∈ S, (a - b, h + (a - b), a) ∈ T := by
  classical
  let e := fourSparse13Equiv G
  have hnew : δ * Fintype.card (G × G) * Fintype.card G ≤
      ((T.map e.toEmbedding).card : ℝ) := by
    rw [Finset.card_map, Fintype.card_prod, Nat.cast_mul]
    convert hsize using 1
    ring
  obtain ⟨⟨a, b⟩, S, hS, hSsize, hmem⟩ := exists_dense_pair_slice (T.map e.toEmbedding) hδ hnew
  refine ⟨a, b, S, hS, hSsize, ?_⟩
  intro h hh
  obtain ⟨t, ht, he⟩ := Finset.mem_map.mp (hmem h hh)
  have hinv : e.symm ((a, b), h) = t := by
    rw [← he]
    exact e.symm_apply_apply t
  change e.symm ((a, b), h) ∈ T
  rwa [hinv]

end Erdos3

end

end OAI
