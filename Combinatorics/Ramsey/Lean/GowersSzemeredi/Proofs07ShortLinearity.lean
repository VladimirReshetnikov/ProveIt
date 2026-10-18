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
  by_cases htwo : A.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
    let a := (phi y - phi x) / (y - x)
    refine ⟨a, phi x - a * x, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · ring
    · have hzy := Finset.mem_singleton.mp hz
      subst z
      dsimp [a]
      field_simp [sub_ne_zero.mpr hxy.symm]
      ring
  have hone : A.card ≤ 1 := by omega
  by_cases hne : A.Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine ⟨0, phi x, ?_⟩
    intro y hy
    have hyx : y = x := Finset.card_le_one.mp hone y hy x hx
    simp [hyx]
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    exact ⟨0, 0, fun _ h ↦ (Finset.notMem_empty _ h).elim⟩

end LeanProofs.GowersSzemeredi
