import GowersSzemeredi.Sections17_18
import Mathlib.Combinatorics.Pigeonhole

/-! The common pigeonhole step for the two-color and general-color conclusions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Some color class of `[1,N]` has at least `N/r` elements. -/
theorem exists_color_class_ge {r : Nat} (hr : 0 < r) (N : Nat) (color : Nat → Fin r) :
    ∃ c : Fin r, (N : Real) / r ≤
      (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) := by
  classical
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Finset.Icc 1 N) (t := Finset.univ) (f := color) (b := (N : Real) / r)
    (fun _ _ => Finset.mem_univ _) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
    (by simp [nsmul_eq_mul, mul_div_cancel₀ _ hrR.ne'])
  exact ⟨c, hc⟩

end LeanProofs.GowersSzemeredi
