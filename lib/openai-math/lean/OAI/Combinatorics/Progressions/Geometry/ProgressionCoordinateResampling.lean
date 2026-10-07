import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G R : Type*} [DecidableEq R] {X : G → R → Type*}

def resampleGroupCoordinates (label : G → R) (c : ∀ g r, X g r)
    (t : ∀ g, X g (label g)) : ∀ g r, X g r :=
  fun g => Function.update (c g) (label g) (t g)

@[simp] theorem resampleGroupCoordinates_selected (label : G → R)
    (c : ∀ g r, X g r) (t : ∀ g, X g (label g)) (g : G) :
    resampleGroupCoordinates label c t g (label g) = t g := by
  simp only [resampleGroupCoordinates, Function.update_self]

def groupCoordinateResamplingEquiv (label : G → R) :
    ((∀ g r, X g r) × (∀ g, X g (label g))) ≃
      ((∀ g r, X g r) × (∀ g, X g (label g))) where
  toFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  invFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  left_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g
  right_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g

theorem expect_resampleGroupCoordinates [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) :
    (𝔼 c : ∀ g r, X g r, 𝔼 t : ∀ g, X g (label g),
      F (resampleGroupCoordinates label c t)) = 𝔼 c : ∀ g r, X g r, F c := by
  have he := Fintype.expect_equiv (groupCoordinateResamplingEquiv (X := X) label)
    (fun p => F (resampleGroupCoordinates label p.1 p.2)) (fun p => F p.1)
    (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

theorem exists_frozen_group_bias [Fintype G] [DecidableEq G] [Fintype R]
    [∀ g r, Fintype (X g r)] [∀ g r, Nonempty (X g r)]
    (label : G → R) (F : (∀ g r, X g r) → ℂ) {ζ : ℝ}
    (hζ : ζ ≤ ‖𝔼 c : ∀ g r, X g r, F c‖) :
    ∃ c : ∀ g r, X g r,
      ζ ≤ ‖𝔼 t : ∀ g, X g (label g), F (resampleGroupCoordinates label c t)‖ := by
  rw [← expect_resampleGroupCoordinates label F] at hζ
  have h := hζ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty h
  exact ⟨c, hc⟩

end Erdos3

end

section

namespace Erdos3

theorem intervalCoordinates_resample {G R : Type*} [DecidableEq R]
    (N : G → R → ℕ) (u : G → R → ℝ) (label : G → R)
    (c : ∀ g r, Fin (N g r)) (t : ∀ g, Fin (N g (label g))) :
    resampleGroupCoordinates label (fun g r => u g r+((c g r).val : ℝ))
      (fun g => u g (label g)+((t g).val : ℝ)) =
        (fun g r => u g r+((resampleGroupCoordinates label c t g r).val : ℝ)) := by
  funext g r
  by_cases hr : r = label g
  · subst r
    simp [resampleGroupCoordinates]
  · simp [resampleGroupCoordinates, hr]

end Erdos3

end

section

namespace Erdos3

theorem progressionCoordinates_resample {G R : Type*} [DecidableEq R]
    (N : G → R → ℕ) (u v : G → R → ℝ) (label : G → R)
    (c : ∀ g r, Fin (N g r)) (t : ∀ g, Fin (N g (label g))) :
    resampleGroupCoordinates label (fun g r => u g r+v g r*((c g r).val : ℝ))
      (fun g => u g (label g)+v g (label g)*((t g).val : ℝ)) =
        (fun g r => u g r+v g r*((resampleGroupCoordinates label c t g r).val : ℝ)) := by
  funext g r
  by_cases hr : r = label g
  · subst r
    simp [resampleGroupCoordinates]
  · simp [resampleGroupCoordinates, hr]

end Erdos3

end

end OAI
