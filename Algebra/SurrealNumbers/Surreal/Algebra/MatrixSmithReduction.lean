import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basic

/-!
# Solving matrix equations after a unimodular diagonal reduction

Generic matrix algebra for `odg:thm:smith`. A chosen rectangular diagonal
form has a common pivot index and separate zero-row and free-column indices.
The source supplies unimodular change-of-basis matrices; these are represented
by native matrix units and remain invertible after mapping the coefficients.
-/

namespace Surreal.MatrixSmithReduction

open Matrix

variable {R S m n κ ρ ν : Type*} [CommRing R] [CommRing S]

/-- An invertible matrix over the coefficient ring acts bijectively after scalar extension. -/
def unitMatrixEquiv [Fintype n] [DecidableEq n] (f : R →+* S) (V : (Matrix n n R)ˣ) :
    (n → S) ≃ (n → S) where
  toFun x := (V.val.map f) *ᵥ x
  invFun x := ((↑(V⁻¹) : Matrix n n R).map f) *ᵥ x
  left_inv x := by
    dsimp only
    rw [mulVec_mulVec, ← Matrix.map_mul]
    simp
  right_inv x := by
    dsimp only
    rw [mulVec_mulVec, ← Matrix.map_mul]
    simp

/-- The chosen two-sided matrix reduction is equivalent to the transformed system. -/
theorem transformed_equation_iff [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : R →+* S) (M D : Matrix m n R) (U : (Matrix m m R)ˣ) (V : (Matrix n n R)ˣ)
    (hD : U.val * M * V.val = D) (b : m → S) (y : n → S) :
    M.map f *ᵥ unitMatrixEquiv f V y = b ↔
      D.map f *ᵥ y = unitMatrixEquiv f U b := by
  rw [← (unitMatrixEquiv f U).injective.eq_iff]
  change U.val.map f *ᵥ (M.map f *ᵥ (V.val.map f *ᵥ y)) = U.val.map f *ᵥ b ↔ _
  rw [mulVec_mulVec, mulVec_mulVec,
    ← Matrix.map_mul, ← Matrix.map_mul, hD]
  rfl

/-- All original solutions are exactly the images of the solutions of the transformed system. -/
theorem solution_iff [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : R →+* S) (M D : Matrix m n R) (U : (Matrix m m R)ˣ) (V : (Matrix n n R)ˣ)
    (hD : U.val * M * V.val = D) (b : m → S) (x : n → S) :
    M.map f *ᵥ x = b ↔ ∃ y, x = unitMatrixEquiv f V y ∧
      D.map f *ᵥ y = unitMatrixEquiv f U b := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (unitMatrixEquiv f V).surjective x
    exact ⟨y, rfl, (transformed_equation_iff f M D U V hD b y).mp hx⟩
  · rintro ⟨y, rfl, hy⟩
    exact (transformed_equation_iff f M D U V hD b y).mpr hy

/-- A rectangular diagonal block, with all extra rows and columns zero. -/
def diagonalBlock [DecidableEq κ] (d : κ → R) : Matrix (κ ⊕ ρ) (κ ⊕ ν) R :=
  Matrix.fromBlocks (Matrix.diagonal d) 0 0 0

/-- Coefficient maps preserve the rectangular diagonal shape. -/
theorem diagonalBlock_map [DecidableEq κ] (f : R →+* S) (d : κ → R) :
    (diagonalBlock (ρ := ρ) (ν := ν) d).map f = diagonalBlock (f ∘ d) := by
  ext i j
  cases i <;> cases j <;> simp [diagonalBlock, Matrix.diagonal, apply_ite f]

/-- A diagonal equation constrains each pivot and every zero row, leaving extra columns free. -/
theorem diagonalBlock_equation_iff [Fintype κ] [Fintype ν] [DecidableEq κ]
    (d : κ → R) (c : κ ⊕ ρ → R) (y : κ ⊕ ν → R) :
    diagonalBlock d *ᵥ y = c ↔
      (∀ i, d i * y (Sum.inl i) = c (Sum.inl i)) ∧ ∀ j, c (Sum.inr j) = 0 := by
  simp only [diagonalBlock, fromBlocks_mulVec, zero_mulVec, add_zero]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [Sum.elim_inl, mulVec_diagonal, Function.comp_apply] using congrFun h (Sum.inl i)
    · intro j
      exact (congrFun h (Sum.inr j)).symm
  · rintro ⟨hp, hz⟩
    funext i
    cases i with
    | inl i => simpa only [Sum.elim_inl, mulVec_diagonal, Function.comp_apply] using hp i
    | inr j => exact (hz j).symm

end Surreal.MatrixSmithReduction
