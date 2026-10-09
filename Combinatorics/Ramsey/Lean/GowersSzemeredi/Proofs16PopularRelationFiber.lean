import GowersSzemeredi.Proofs16RelationAveraging

/-! Direct fibre averaging for a popular relation. Fixing one coordinate
retains the pair density, without squaring it by Cauchy--Schwarz. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A matching relation on many pairs has a fibre of at least the same
relative density in the first vertex class. -/
theorem exists_popular_matching_fiber {X Y Z : Type*} [DecidableEq X] [DecidableEq Y]
    [DecidableEq Z] (C : Finset X) (D : Finset Y) (hD : D.Nonempty)
    (f : X → Z) (g : Y → Z) {theta : Real}
    (hpairs : theta * C.card * D.card ≤
      (((C ×ˢ D).filter fun p => f p.1 = g p.2).card : Real)) :
    ∃ y ∈ D, theta * C.card ≤ ((C.filter fun x => f x = g y).card : Real) := by
  have hsum : (∑ y ∈ D, ((C.filter fun x => f x = g y).card : Real)) =
      (((C ×ˢ D).filter fun p => f p.1 = g p.2).card : Real) := by
    simp only [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    rw [Finset.sum_comm]
  by_contra hno
  push Not at hno
  have hlt : (∑ y ∈ D, ((C.filter fun x => f x = g y).card : Real)) <
      ∑ _y ∈ D, theta * (C.card : Real) :=
    Finset.sum_lt_sum_of_nonempty hD (fun y hy => hno y hy)
  rw [hsum, Finset.sum_const, nsmul_eq_mul] at hlt
  nlinarith only [hpairs, hlt]

end LeanProofs.GowersSzemeredi
