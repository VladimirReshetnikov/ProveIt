import GowersSzemeredi.Proofs07ModularPartition

/-!
# Affine linearity on short progressions

This module keeps `linearOn_of_card_le_two`; the rest of the development, with
its description, is in `Proofs07ShortLinearitySide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- Any map on at most two points of a prime field agrees with an affine map. -/
theorem linearOn_of_card_le_two {N : Nat} [Fact N.Prime]
    (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (hA : A.card ≤ 2) :
    LinearOn A phi := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨0, 0, fun _ h ↦ (Finset.notMem_empty _ h).elim⟩
  by_cases hone : A.card ≤ 1
  · exact ⟨0, phi x, fun y hy ↦ by simp [Finset.card_le_one.mp hone y hy x hx]⟩
  -- two points `u ≠ v`: take the line through `(u, phi u)` and `(v, phi v)`
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (by omega : A.card = 2)
  refine ⟨(phi v - phi u) / (v - u), phi u - (phi v - phi u) / (v - u) * u, fun z hz ↦ ?_⟩
  rcases Finset.mem_insert.mp hz with rfl | hz
  · ring
  · rw [Finset.mem_singleton.mp hz]
    field_simp [sub_ne_zero.mpr huv.symm]
    ring

end LeanProofs.GowersSzemeredi
