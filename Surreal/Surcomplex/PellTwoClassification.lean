import Surreal.Algebra.PellTwo
import Surreal.Surcomplex.PellRigidity

/-!
# All omnific solutions of the classical Pell equation

The full `odg:ex:pell2`. Omnific rigidity first reduces to ordinary integer
solutions. Mathlib's Pell theory and the explicitly verified fundamental
solution (3,2) then give the natural-power sequence with independent signs.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Every actual omnific solution is an independently signed ordinary natural power of
3 + 2 sqrt(2), and every such signed power is a solution. -/
theorem omnific_pell_two_classification (x y : SignSequence.OmnificInteger.{u}) :
    x ^ 2 - SignSequence.omnificIntCast 2 * y ^ 2 = SignSequence.omnificIntCast 1 ↔
      ∃ k : ℕ,
        (x = SignSequence.omnificIntCast (PellTwo.X k) ∨
          x = -SignSequence.omnificIntCast (PellTwo.X k)) ∧
        (y = SignSequence.omnificIntCast (PellTwo.Y k) ∨
          y = -SignSequence.omnificIntCast (PellTwo.Y k)) := by
  rw [omnific_pell_solutions_iff 2 1 (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨a, b, he, rfl, rfl⟩
    obtain ⟨k, hx, hy⟩ := (PellTwo.integer_solutions_iff a b).mp he
    refine ⟨k, ?_, ?_⟩
    · rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (map_neg _ _)
    · rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (map_neg _ _)
  · rintro ⟨k, hx, hy⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨PellTwo.X k, PellTwo.Y k, PellTwo.equation k, rfl, rfl⟩
    · exact ⟨PellTwo.X k, -PellTwo.Y k, by simpa only [neg_sq] using PellTwo.equation k,
        rfl, (map_neg _ _).symm⟩
    · exact ⟨-PellTwo.X k, PellTwo.Y k, by simpa only [neg_sq] using PellTwo.equation k,
        (map_neg _ _).symm, rfl⟩
    · exact ⟨-PellTwo.X k, -PellTwo.Y k, by simpa only [neg_sq] using PellTwo.equation k,
        (map_neg _ _).symm, (map_neg _ _).symm⟩

end
end Surreal.Surcomplex
