import OAI.Combinatorics.Progressions.Lattices.AffineMeshRetention

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped Classical
variable {J : Type*} {N : J → ℕ} {q : ℕ}

theorem length_le_parent (S : ResidueBoxSlice N q) (hq : 0 < q) (j : J) :
    S.length j ≤ N j := by
  by_cases hl : 0 < S.length j
  · have hi := S.inside j (S.length j - 1) (by omega)
    have hm : S.length j - 1 ≤ q * (S.length j - 1) := by
      exact Nat.le_mul_of_pos_left _ hq
    omega
  · omega

theorem scalarRectangle_geometry (S : ResidueBoxSlice N q) (hq : 0 < q)
    {L density ratio : ℝ} (hL : 1 ≤ L) (hdensity : 0 < density)
    (hratio : 1 ≤ ratio) (hlong : 4 ≤ density * L)
    (hN : ∀ j, (N j : ℝ) ≤ ratio * L)
    (hlength : ∀ j, density * L / 2 ≤ (S.length j : ℝ)) :
    (∀ j, 2 ≤ S.length j) ∧
    (∀ j, S.length j ≤ ⌈ratio * L⌉₊) ∧
    (⌈ratio * L⌉₊ : ℝ) ≤ (4 * ratio / density) * (density * L / 2) ∧
    (∀ j, |(S.start j : ℝ) / L| ≤ 2 * ratio) ∧
    (∀ j, |((S.start j : ℝ) + (q : ℝ) * S.length j) / L| ≤ 2 * ratio) := by
  have hLpos : 0 < L := by linarith
  have hratio0 : 0 ≤ ratio := by linarith
  have hlen2 (j) : 2 ≤ S.length j := by
    exact_mod_cast (show (2 : ℝ) ≤ S.length j by linarith [hlength j])
  refine ⟨hlen2, ?_, ?_, ?_, ?_⟩
  · intro j
    exact_mod_cast ((Nat.cast_le.mpr (S.length_le_parent hq j) :
      (S.length j : ℝ) ≤ N j).trans (hN j)).trans (Nat.le_ceil _)
  · have hc : (⌈ratio * L⌉₊ : ℝ) ≤ ratio * L + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hratio0 hLpos.le)).le
    have hprod : 1 ≤ ratio * L := one_le_mul_of_one_le_of_one_le hratio hL
    have he : (4 * ratio / density) * (density * L / 2) = 2 * ratio * L := by
      field_simp
      ring
    rw [he]
    linarith
  · intro j
    exact (S.fullSliceRectangle_endpoint_bounds_two hlen2 hLpos hN j).1.trans
      (by linarith)
  · intro j
    exact (S.fullSliceRectangle_endpoint_bounds_two hlen2 hLpos hN j).2

end Erdos3.ResidueBoxSlice

end

end OAI
