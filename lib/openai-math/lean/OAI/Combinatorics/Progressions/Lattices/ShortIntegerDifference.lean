import Mathlib

namespace OAI

section

namespace Erdos3

theorem exists_short_integer_difference (D : Finset ℤ) {H Q : ℕ} (hQ : 0 < Q)
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ)) (hcard : 2 * H / Q + 1 < D.card) :
    ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x < (Q : ℤ) := by
  let f : ℤ → ℤ := fun h => (h + (H : ℤ)) / (Q : ℤ)
  let B := Finset.Icc (0 : ℤ) ((2 * H / Q : ℕ) : ℤ)
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmap : ∀ h ∈ D, f h ∈ B := by
    intro h hh
    have hd := abs_le.mp (hD h hh)
    simp only [B, f, Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by omega) hQ'.le
    · have hl : h + (H : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by omega
      exact_mod_cast Int.ediv_le_ediv hQ' hl
  have hB : B.card = 2 * H / Q + 1 := by
    simp only [B, Int.card_Icc, sub_zero]
    norm_cast
  obtain ⟨x, hx, y, hy, hxy, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rwa [hB] : B.card < D.card) hmap
  have hdif : |x - y| < (Q : ℤ) := by
    have hxrem := Int.emod_nonneg (x + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hyrem := Int.emod_nonneg (y + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hxlt := Int.emod_lt_of_pos (x + (H : ℤ)) hQ'
    have hylt := Int.emod_lt_of_pos (y + (H : ℤ)) hQ'
    have hxdiv := Int.emod_add_ediv_mul (x + (H : ℤ)) (Q : ℤ)
    have hydiv := Int.emod_add_ediv_mul (y + (H : ℤ)) (Q : ℤ)
    change (x + (H : ℤ)) / Q = (y + (H : ℤ)) / Q at heq
    rw [heq] at hxdiv
    rw [abs_lt]
    constructor <;> omega
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact ⟨x, hx, y, hy, hxy, by have := abs_lt.mp hdif; omega⟩
  · exact ⟨y, hy, x, hx, hxy, by have := abs_lt.mp hdif; omega⟩

end Erdos3

end

end OAI
