import Surreal.Foundations.OmnificResidues
import Surreal.Algebra.MatrixSmithReduction

/-!
# The omnific Smith-normal-form solution criterion

The theorem `odg:thm:smith` and formula `odg:eq:smithcriterion`, given the
chosen integer diagonal reduction in the source. Pivot, zero-row and
free-column indices are separate finite types, covering rectangular and
rank-zero systems. Nonzero pivots suffice; positivity and the ordering of
Smith invariant factors are not needed for the solution criterion.
-/

universe u v w z
namespace Surreal.Foundations.SignSequence

open Matrix MatrixSmithReduction

noncomputable section

/-- The field quotient is the unique solution of a nonzero integer pivot equation. -/
theorem omnific_pivot_equation_iff (d : ℤ) (hd : d ≠ 0) (c y : OmnificInteger.{u}) :
    omnificIntCast d * y = c ↔ omnificToSurreal y = omnificToSurreal c / (d : SignSequence) := by
  have hd' : (d : SignSequence.{u}) ≠ 0 := by exact_mod_cast hd
  rw [eq_div_iff hd']
  constructor
  · intro h
    simpa only [map_mul, omnificToSurreal_intCast, mul_comm] using congrArg omnificToSurreal h
  · intro h
    apply omnificToSurreal_injective
    simpa only [map_mul, omnificToSurreal_intCast, mul_comm] using h

variable {κ : Type v} {ρ : Type w} {ν : Type z}
variable [Fintype κ] [Fintype ν] [DecidableEq κ]

/-- Solvability of the diagonal system depends on constant divisibility and exact zero rows. -/
theorem omnific_diagonal_solvable_iff (d : κ → ℤ) (hd : ∀ i, d i ≠ 0)
    (c : κ ⊕ ρ → OmnificInteger.{u}) :
    (∃ y : κ ⊕ ν → OmnificInteger, (diagonalBlock d).map omnificIntCast *ᵥ y = c) ↔
      (∀ i, d i ∣ omnificConstantCoeff (c (Sum.inl i))) ∧ ∀ j, c (Sum.inr j) = 0 := by
  simp only [diagonalBlock_map]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hp, hz⟩ := (diagonalBlock_equation_iff _ _ _).mp hy
    exact ⟨fun i => (omnific_int_dvd_iff _ (hd i) _).mp ⟨y (Sum.inl i), (hp i).symm⟩, hz⟩
  · rintro ⟨hp, hz⟩
    have hq (i : κ) : ∃ q : OmnificInteger.{u}, c (Sum.inl i) = omnificIntCast (d i) * q :=
      (omnific_int_dvd_iff _ (hd i) _).mpr (hp i)
    choose q hq using hq
    refine ⟨Sum.elim q (fun _ => 0), (diagonalBlock_equation_iff _ _ _).mpr ?_⟩
    exact ⟨fun i => (hq i).symm, hz⟩

/-- Prescribing arbitrary free coordinates determines exactly one diagonal solution whenever
the solvability criterion holds. -/
theorem omnific_diagonal_free_coordinates (d : κ → ℤ) (hd : ∀ i, d i ≠ 0)
    (c : κ ⊕ ρ → OmnificInteger.{u})
    (hc : (∀ i, d i ∣ omnificConstantCoeff (c (Sum.inl i))) ∧ ∀ j, c (Sum.inr j) = 0)
    (a : ν → OmnificInteger.{u}) :
    ∃! y : κ ⊕ ν → OmnificInteger,
      (diagonalBlock d).map omnificIntCast *ᵥ y = c ∧ ∀ j, y (Sum.inr j) = a j := by
  obtain ⟨q, hq⟩ := (omnific_diagonal_solvable_iff (ν := ν) d hd c).mpr hc
  rw [diagonalBlock_map] at hq
  obtain ⟨hp, hz⟩ := (diagonalBlock_equation_iff _ _ _).mp hq
  let y := Sum.elim (fun i => q (Sum.inl i)) a
  refine ⟨y, ⟨?_, fun _ => rfl⟩, ?_⟩
  · rw [diagonalBlock_map, diagonalBlock_equation_iff]
    exact ⟨hp, hz⟩
  · rintro y' ⟨hy', ha⟩
    rw [diagonalBlock_map, diagonalBlock_equation_iff] at hy'
    funext i
    cases i with
    | inl i =>
      apply omnificToSurreal_injective
      exact ((omnific_pivot_equation_iff _ (hd i) _ _).mp (hy'.1 i)).trans
        ((omnific_pivot_equation_iff _ (hd i) _ _).mp (hp i)).symm
    | inr j => exact ha j

variable [Fintype ρ] [DecidableEq ρ] [DecidableEq ν]

/-- All solutions of a chosen integer Smith reduction: the pivot coordinates are field
quotients, and no condition is imposed on the free-column coordinates. -/
theorem omnific_smith_all_solutions
    (M : Matrix (κ ⊕ ρ) (κ ⊕ ν) ℤ)
    (U : (Matrix (κ ⊕ ρ) (κ ⊕ ρ) ℤ)ˣ) (V : (Matrix (κ ⊕ ν) (κ ⊕ ν) ℤ)ˣ)
    (d : κ → ℤ) (hd : ∀ i, d i ≠ 0) (hD : U.val * M * V.val = diagonalBlock d)
    (b : κ ⊕ ρ → OmnificInteger.{u}) (x : κ ⊕ ν → OmnificInteger) :
    M.map omnificIntCast *ᵥ x = b ↔
      ∃ y : κ ⊕ ν → OmnificInteger, x = unitMatrixEquiv omnificIntCast V y ∧
        (∀ i, omnificToSurreal (y (Sum.inl i)) =
          omnificToSurreal (unitMatrixEquiv omnificIntCast U b (Sum.inl i)) / (d i : SignSequence)) ∧
        ∀ j, unitMatrixEquiv omnificIntCast U b (Sum.inr j) = 0 := by
  rw [solution_iff omnificIntCast M (diagonalBlock d) U V hD b x]
  simp only [diagonalBlock_map, diagonalBlock_equation_iff, Function.comp_apply,
    omnific_pivot_equation_iff _ (hd _)]

/-- The complete solvability criterion for the chosen rectangular Smith normal form. -/
theorem omnific_smith_solvable_iff
    (M : Matrix (κ ⊕ ρ) (κ ⊕ ν) ℤ)
    (U : (Matrix (κ ⊕ ρ) (κ ⊕ ρ) ℤ)ˣ) (V : (Matrix (κ ⊕ ν) (κ ⊕ ν) ℤ)ˣ)
    (d : κ → ℤ) (hd : ∀ i, d i ≠ 0) (hD : U.val * M * V.val = diagonalBlock d)
    (b : κ ⊕ ρ → OmnificInteger.{u}) :
    (∃ x : κ ⊕ ν → OmnificInteger, M.map omnificIntCast *ᵥ x = b) ↔
      (∀ i, d i ∣ omnificConstantCoeff (unitMatrixEquiv omnificIntCast U b (Sum.inl i))) ∧
      ∀ j, unitMatrixEquiv omnificIntCast U b (Sum.inr j) = 0 := by
  rw [← omnific_diagonal_solvable_iff (ν := ν) d hd]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (unitMatrixEquiv omnificIntCast V).surjective x
    exact ⟨y, (transformed_equation_iff omnificIntCast M _ U V hD b y).mp hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨unitMatrixEquiv omnificIntCast V y,
      (transformed_equation_iff omnificIntCast M _ U V hD b y).mpr hy⟩

end
end Surreal.Foundations.SignSequence
