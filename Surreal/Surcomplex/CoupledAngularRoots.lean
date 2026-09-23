import Surreal.Algebra.CoupledQuadraticAlgebra
import Surreal.Surcomplex.CosineFold
import Surreal.Surcomplex.QuadraticCollisionPoints

/-!
# The complete zero set of the coupled angular collision

For `trigonometry:eq:coupled`, `trigonometry:eq:coupleddiagonal` and
`trigonometry:eq:coupledroots`, the sine coordinates identify the actual
infinitesimal angle solutions with a product of two unrestricted square-root
sets. This gives all branches and the exact number of distinct complex
solutions, including both collision strata. Local algebra multiplicities
are proved in `CoupledAngularMultiplicity.lean`.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

open Foundations CosineFold

noncomputable section

/-- The pair of equations before diagonalizing the sine coordinates. -/
def Equations (s t x y : Surcomplex.{u}) : Prop := x ^ 2 + y ^ 2 = s ∧ x * y = t

/-- The linear coordinate change diagonalizes the two equations exactly. -/
theorem equations_iff (s t x y : Surcomplex.{u}) :
    Equations s t x y ↔ (x + y) ^ 2 = s + 2 * t ∧ (x - y) ^ 2 = s - 2 * t := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · linear_combination h₁ + 2 * h₂
    · linear_combination h₁ - 2 * h₂
  · rintro ⟨h₁, h₂⟩
    constructor
    · linear_combination (h₁ + h₂) / 2
    · linear_combination (h₁ - h₂) / 4

/-- The inverse linear coordinates satisfy the original system. -/
theorem equations_half (s t X Y : Surcomplex.{u})
    (hX : X ^ 2 = s + 2 * t) (hY : Y ^ 2 = s - 2 * t) :
    Equations s t ((X + Y) / 2) ((X - Y) / 2) := by
  apply (equations_iff _ _ _ _).mpr
  have h₁ : (X + Y) / 2 + (X - Y) / 2 = X := by ring
  have h₂ : (X + Y) / 2 - (X - Y) / 2 = Y := by ring
  exact ⟨by rw [h₁]; exact hX, by rw [h₂]; exact hY⟩

/-- Infinitesimal angle pairs satisfying the original analytic equations. -/
abbrev Solutions (s t : Surcomplex.{u}) :=
  {p : {z : Surcomplex.{u} // IsInfinitesimal z} ×
      {z : Surcomplex.{u} // IsInfinitesimal z} //
    Equations s t (infSin p.1.1 p.1.2) (infSin p.2.1 p.2.2)}

/-- No infinitesimal restriction is imposed on the algebraic roots. It follows
from their squares and the parameter hypotheses. -/
abbrev DiagonalRoots (s t : Surcomplex.{u}) :=
  {X : Surcomplex.{u} // X ^ 2 = s + 2 * t} ×
  {Y : Surcomplex.{u} // Y ^ 2 = s - 2 * t}

theorem infinitesimal_left_root {s t X : Surcomplex.{u}}
    (hs : IsInfinitesimal s) (ht : IsInfinitesimal t) (hX : X ^ 2 = s + 2 * t) :
    IsInfinitesimal X :=
  infinitesimal_of_sq_eq hX (infinitesimal_add hs (infinitesimal_two_mul ht))

theorem infinitesimal_right_root {s t Y : Surcomplex.{u}}
    (hs : IsInfinitesimal s) (ht : IsInfinitesimal t) (hY : Y ^ 2 = s - 2 * t) :
    IsInfinitesimal Y :=
  infinitesimal_of_sq_eq hY (by
    rw [sub_eq_add_neg]
    exact infinitesimal_add hs (infinitesimal_neg (infinitesimal_two_mul ht)))

/-- The two literal inverse-sine arguments in the source root formula. -/
def sineCoordinates (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) (r : DiagonalRoots s t) :
    {z : Surcomplex.{u} // IsInfinitesimal z} ×
      {z : Surcomplex.{u} // IsInfinitesimal z} :=
  let hX := infinitesimal_left_root hs ht r.1.2
  let hY := infinitesimal_right_root hs ht r.2.2
  (⟨(r.1.1 + r.2.1) / 2, infinitesimal_div_two (infinitesimal_add hX hY)⟩,
   ⟨(r.1.1 - r.2.1) / 2, infinitesimal_div_two (by
     rw [sub_eq_add_neg]; exact infinitesimal_add hX (infinitesimal_neg hY))⟩)

/-- Every pair of square roots gives an actual angular solution by arcsine. -/
def anglesOfRoots (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) (r : DiagonalRoots s t) : Solutions s t := by
  let c := sineCoordinates s t hs ht r
  refine ⟨(infinitesimalSinEquiv.symm c.1, infinitesimalSinEquiv.symm c.2), ?_⟩
  change Equations s t (infSin (infArcsin c.1.1 c.1.2) _)
    (infSin (infArcsin c.2.1 c.2.2) _)
  rw [infSin_infArcsin, infSin_infArcsin]
  exact equations_half s t r.1.1 r.2.1 r.1.2 r.2.2

/-- All infinitesimal angular solutions correspond bijectively to the full
algebraic zero set, including at collisions. -/
def solutionsEquiv (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) : Solutions s t ≃ DiagonalRoots s t where
  toFun p :=
    (⟨infSin p.1.1.1 p.1.1.2 + infSin p.1.2.1 p.1.2.2,
      ((equations_iff _ _ _ _).mp p.2).1⟩,
     ⟨infSin p.1.1.1 p.1.1.2 - infSin p.1.2.1 p.1.2.2,
      ((equations_iff _ _ _ _).mp p.2).2⟩)
  invFun := anglesOfRoots s t hs ht
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · change infArcsin ((_ + _ + (_ - _)) / 2) _ = _
      have he : (infSin p.1.1.1 p.1.1.2 + infSin p.1.2.1 p.1.2.2 +
          (infSin p.1.1.1 p.1.1.2 - infSin p.1.2.1 p.1.2.2)) / 2 =
          infSin p.1.1.1 p.1.1.2 := by ring
      calc
        _ = infArcsin (infSin p.1.1.1 p.1.1.2) _ := by congr 1
        _ = _ := infArcsin_infSin _ _
    · change infArcsin ((_ + _ - (_ - _)) / 2) _ = _
      have he : (infSin p.1.1.1 p.1.1.2 + infSin p.1.2.1 p.1.2.2 -
          (infSin p.1.1.1 p.1.1.2 - infSin p.1.2.1 p.1.2.2)) / 2 =
          infSin p.1.2.1 p.1.2.2 := by ring
      calc
        _ = infArcsin (infSin p.1.2.1 p.1.2.2) _ := by congr 1
        _ = _ := infArcsin_infSin _ _
  right_inv r := by
    apply Prod.ext <;> apply Subtype.ext
    · change infSin (infArcsin _ _) _ + infSin (infArcsin _ _) _ = _
      rw [infSin_infArcsin, infSin_infArcsin]
      change (r.1.1 + r.2.1) / 2 + (r.1.1 - r.2.1) / 2 = r.1.1
      ring
    · change infSin (infArcsin _ _) _ - infSin (infArcsin _ _) _ = _
      rw [infSin_infArcsin, infSin_infArcsin]
      change (r.1.1 + r.2.1) / 2 - (r.1.1 - r.2.1) / 2 = r.2.1
      ring

/-- The branch formula is literally the two inverse sines displayed in the report. -/
theorem anglesOfRoots_coordinates (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) (r : DiagonalRoots s t) :
    (anglesOfRoots s t hs ht r).1.1.1 =
      infArcsin ((r.1.1 + r.2.1) / 2) (sineCoordinates s t hs ht r).1.2 ∧
    (anglesOfRoots s t hs ht r).1.2.1 =
      infArcsin ((r.1.1 - r.2.1) / 2) (sineCoordinates s t hs ht r).2.2 := ⟨rfl, rfl⟩

/-- Independent choices of the two square-root signs exhaust all branches. -/
theorem diagonal_roots_iff (s t X Y p q : Surcomplex.{u})
    (hp : p ^ 2 = s + 2 * t) (hq : q ^ 2 = s - 2 * t) :
    (X ^ 2 = s + 2 * t ∧ Y ^ 2 = s - 2 * t) ↔
      (X = p ∨ X = -p) ∧ (Y = q ∨ Y = -q) := by
  rw [← hp, ← hq, sq_eq_sq_iff_eq_or_eq_neg, sq_eq_sq_iff_eq_or_eq_neg]

/-- The zero parameter has one square root; every nonzero parameter has two. -/
theorem card_square_roots (d : Surcomplex.{u}) :
    Nat.card {z : Surcomplex.{u} // z ^ 2 = d} = if d = 0 then 1 else 2 := by
  split_ifs with hd
  · subst d
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, by simp⟩, ?_⟩
    intro z
    apply Subtype.ext
    simpa using z.2
  · exact QuadraticCollision.card_points d hd

/-- The exact number of distinct complex angular solutions is four, two or
one, according to which diagonal parameters vanish. -/
theorem card_solutions (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) :
    Nat.card (Solutions s t) =
      (if s + 2 * t = 0 then 1 else 2) * (if s - 2 * t = 0 then 1 else 2) := by
  rw [Nat.card_congr (solutionsEquiv s t hs ht)]
  exact (Nat.card_prod _ _).trans (by rw [card_square_roots, card_square_roots])

/-- There are four distinct complex solutions off both diagonal collisions. -/
theorem card_solutions_four (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) (h₁ : s + 2 * t ≠ 0) (h₂ : s - 2 * t ≠ 0) :
    Nat.card (Solutions s t) = 4 := by
  simp [card_solutions s t hs ht, h₁, h₂]

/-- Exactly one vanishing diagonal parameter leaves two distinct angular solutions. -/
theorem card_solutions_two (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t)
    (h : (s + 2 * t = 0 ∧ s - 2 * t ≠ 0) ∨
      (s + 2 * t ≠ 0 ∧ s - 2 * t = 0)) : Nat.card (Solutions s t) = 2 := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [card_solutions s t hs ht, h₁, h₂]

/-- The common collision has exactly one point. Its algebra still has rank four. -/
theorem card_solutions_zero : Nat.card (Solutions (0 : Surcomplex.{u}) 0) = 1 := by
  simp [card_solutions 0 0 infinitesimal_zero infinitesimal_zero]

/-- The simultaneous collision is precisely the zero parameter pair. -/
theorem both_diagonal_zero_iff (s t : Surcomplex.{u}) :
    (s + 2 * t = 0 ∧ s - 2 * t = 0) ↔ s = 0 ∧ t = 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · linear_combination (h₁ + h₂) / 2
    · linear_combination (h₁ - h₂) / 4
  · rintro ⟨rfl, rfl⟩; simp

/-- The finite intersection algebra represents precisely the angular points
when evaluated in the actual surcomplex field. -/
def homEquivSolutions (s t : Surcomplex.{u}) (hs : IsInfinitesimal s)
    (ht : IsInfinitesimal t) :
    (FinitePolynomial.coupledQuotient (s + 2 * t) (s - 2 * t) →ₐ[Surcomplex.{u}]
      Surcomplex.{u}) ≃ Solutions s t :=
  (FinitePolynomial.coupledHomEquivRoots (s + 2 * t) (s - 2 * t) Surcomplex.{u}).trans
    (solutionsEquiv s t hs ht).symm

/-- The actual intersection algebra has dimension four at every parameter,
including the common collision where there is just one geometric point. -/
theorem intersection_finrank (s t : Surcomplex.{u}) :
    Module.finrank Surcomplex.{u}
      (FinitePolynomial.coupledQuotient (s + 2 * t) (s - 2 * t)) = 4 :=
  FinitePolynomial.coupledQuotient_finrank _ _

end
end Surreal.Surcomplex.CoupledAngular
