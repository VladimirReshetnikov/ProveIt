import OAI.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentIndependence

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J X : Type*}

noncomputable def coordinateResamplingEquiv (f : J → I) (hf : Function.Injective f) :
    ((I → X) × (J → X)) ≃ ((I → X) × (J → X)) where
  toFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  invFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j

theorem expect_coordinate_resampling [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype X] [Nonempty X]
    (f : J → I) (hf : Function.Injective f) (F : (I → X) → ℝ) :
    (𝔼 v : I → X, 𝔼 y : J → X, F (Function.extend f y v)) = 𝔼 v : I → X, F v := by
  have he := Fintype.expect_equiv (coordinateResamplingEquiv (X := X) f hf)
    (fun p => F (Function.extend f p.2 p.1)) (fun p => F p.1) (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem expect_uniform_coordinate_refresh {B X : Type*}
    [Fintype B] [DecidableEq B] [Fintype X] [Nonempty X]
    (b : B) (F : (B → X) → ℝ) :
    (𝔼 c : B → X, 𝔼 d : X, F (Function.update c b d)) = 𝔼 c : B → X, F c := by
  let f : Unit → B := fun _ => b
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have he (c : B → X) (d : Unit → X) :
      Function.extend f d c = Function.update c b (d ()) := by
    funext i
    by_cases hi : i = b
    · subst i
      rw [show Function.extend f d c b = d () from hf.extend_apply d c ()]
      simp
    · have hni : i ∉ Set.range f := by
        rintro ⟨j, hj⟩
        exact hi hj.symm
      rw [Function.extend_apply' d c i hni]
      simp [hi]
  have hx (c : B → X) : (𝔼 d : X, F (Function.update c b d)) =
      𝔼 d : Unit → X, F (Function.extend f d c) := by
    apply Fintype.expect_equiv (Equiv.funUnique Unit X).symm
    intro d
    rw [he]
    rfl
  simp_rw [hx]
  exact expect_coordinate_resampling f hf F

theorem expect_uniform_coordinate {B : Type*} [Fintype B] [DecidableEq B]
    {X : B → Type*} [∀ b, Fintype (X b)] [∀ b, Nonempty (X b)]
    (b : B) (F : X b → ℝ) :
    (𝔼 c : ∀ j, X j, F (c b)) = 𝔼 d : X b, F d := by
  have h := uniform_expect_coordinate_pullback (X := X) (fun _ : Unit => b)
    (fun _ _ _ => Subsingleton.elim _ _) (fun y => F (y ()))
  calc
    _ = 𝔼 y : Unit → X b, F (y ()) := h
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.funUnique Unit (X b))
      intro y
      rfl

end Erdos3

end

end OAI
