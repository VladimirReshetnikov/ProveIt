import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K]

theorem expect_affine_class_refinement (e : H →+ G) (d : K →+ H)
    (r : G) (f : G → ℂ) :
    (𝔼 y : H, 𝔼 x : K, f ((r + e y) + e (d x))) =
      𝔼 y : H, f (r + e y) := by
  rw [Finset.expect_comm]
  have hpoint (x : K) : (𝔼 y : H, f ((r + e y) + e (d x))) =
      𝔼 y : H, f (r + e y) := by
    calc
      _ = 𝔼 y : H, f (r + e (d x + y)) := by
        apply Finset.expect_congr rfl
        intro y _
        rw [map_add]
        congr 1
        abel
      _ = _ := expect_translate (fun y => f (r + e y)) (d x)
  simp only [hpoint, Fintype.expect_const]

theorem norm_affine_class_mean_le_of_refinement (e : H →+ G) (d : K →+ H)
    (r : G) (f : G → ℂ) (β : ℝ)
    (hbound : ∀ y : H, ‖𝔼 x : K, f ((r + e y) + e (d x))‖ ≤ β) :
    ‖𝔼 y : H, f (r + e y)‖ ≤ β := by
  rw [← expect_affine_class_refinement e d r f]
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun y _ => hbound y)).trans_eq (Fintype.expect_const β))

def scalarTupleHom {I R : Type*} [CommRing R] (c : R) : (I → R) →+ (I → R) where
  toFun x i := c * x i
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp [mul_add]

theorem norm_scalar_affine_class_mean_le {I R : Type*} [Fintype I]
    [CommRing R] [Fintype R] (e d : R) (r : I → R) (f : (I → R) → ℂ) (β : ℝ)
    (hbound : ∀ t : I → R,
      ‖𝔼 x : I → R, f (fun i => t i + (e * d) * x i)‖ ≤ β) :
    ‖𝔼 y : I → R, f (fun i => r i + e * y i)‖ ≤ β := by
  apply norm_affine_class_mean_le_of_refinement (scalarTupleHom e) (scalarTupleHom d) r f β
  intro y
  change ‖𝔼 x : I → R, f (fun i => (r i + e * y i) + e * (d * x i))‖ ≤ β
  simpa only [mul_assoc] using hbound (fun i => r i + e * y i)

end Erdos3

end

end OAI
