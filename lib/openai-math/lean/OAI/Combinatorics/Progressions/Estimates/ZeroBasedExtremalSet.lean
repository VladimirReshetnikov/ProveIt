import OAI.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter

namespace OAI

section

namespace Erdos3

theorem exists_zero_based_extremalSet {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ APFree (S : Set ℕ) k ∧ S.card = extremalNumber k N := by
  classical
  obtain ⟨S, hS, hfree, hcard⟩ := exists_extremalSet hk N
  let T := S.image (fun n => n - 1)
  have hT : T ⊆ Finset.range N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxs := Finset.mem_Icc.mp (hS hx)
    exact Finset.mem_range.mpr (by omega)
  have hTf : APFree (T : Set ℕ) k := by
    apply (hfree.affine_preimage 1 1 (by omega)).mono
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxs := Finset.mem_Icc.mp (hS hx)
    have he : 1 + 1 * (x - 1) = x := by omega
    simpa only [Set.mem_preimage, he, Finset.mem_coe] using hx
  have hTc : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    have hx1 := (Finset.mem_Icc.mp (hS hx)).1
    have hy1 := (Finset.mem_Icc.mp (hS hy)).1
    change x - 1 = y - 1 at he
    omega
  exact ⟨T, hT, hTf, hTc.trans hcard⟩

end Erdos3

end

end OAI
