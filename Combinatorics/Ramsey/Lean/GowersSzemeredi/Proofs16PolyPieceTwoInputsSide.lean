import GowersSzemeredi.Proofs16PolyPieceTwoInputs
import GowersSzemeredi.Proofs16FreimanFamilyRestrictionSide

/-! Declarations of `Proofs16PolyPieceTwoInputs` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The families of `φ` on `B*` give families of `φ₁` on any domain whose
translated points lie in `B*`. -/
theorem Section16FinalFreimanFamilies.of_translate {N q : Nat} [NeZero N]
    {Bs : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q Bs phi) (x0 : Point N 1)
    (D : Finset (Point N 2))
    (hD : ∀ z ∈ D, appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs) :
    Section16FinalFreimanFamilies q D (section16PhiOne phi x0) := by
  intro t
  have hp := (h t).translate (-x0)
  have heq : (fun y => section16FinalCoordinateRestriction phi t (y - -x0)) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) t := by
    funext y
    simp [section16FinalCoordinateRestriction, section16PhiOne,
      section16Init_appendCoordinate, section16Last_appendCoordinate, sub_neg_eq_add, add_comm]
    rfl
  rw [heq] at hp
  apply hp.mono
  intro y hy
  have hb := hD _ (Finset.mem_filter.mp hy).2
  simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hb
  apply Finset.mem_image.mpr
  refine ⟨y + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩

theorem cubicSlice_count_monotone (q : Nat) :
    Monotone (fun r : Nat => ((3 * (max 1 r * q) : Nat) : Real)) := by
  intro r r' hrr
  dsimp only
  exact_mod_cast Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right q (max_le_max le_rfl hrr))

theorem cubicSlice_exponent_antitone {q : Nat} (hq : 0 < q) {eps : Real} (heps : 0 < eps) :
    Antitone (fun r : Nat => cubicBaseExponent (max 1 r * q) eps) := by
  intro r r' hrr
  dsimp only
  unfold cubicBaseExponent
  have hle : ((max 1 r * q : Nat) : Real) ≤ ((max 1 r' * q : Nat) : Real) := by
    exact_mod_cast Nat.mul_le_mul_right q (max_le_max le_rfl hrr)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) hle 4

end LeanProofs.GowersSzemeredi
