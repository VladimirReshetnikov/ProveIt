import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import Mathlib.RingTheory.Polynomial.Morse
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebra Optimizations
# Repository: ProveIt / VladMath
# Specialist: Algebra Formalizer (Wave 2)
# Target File: `vladmath/Algebra_Optimizations.lean`

This file contains verified, optimized, and standalone formalizations for:
1. **Alpöge's Dimension-3 Polynomial Map** (Refutation of the Jacobian Conjecture):
   - Formalization of the dimension-3 counterexample by Levent Alpöge (2026).
   - Coordinate polynomials `P`, `Q`, `W` over an arbitrary commutative ring `R`.
   - The Collision: Distinct integer points `(-1, 1, 5)` and `(0, -2, -16)` map to `(0, -2, 0)`.
   - Optimized Jacobian determinant calculation via 2×2 minor factorization of Rows 1 and 2
     for Laplace expansion along Row 0:
     - Entries of Row 2: `J₂₀ = 2 - 6xy - 3x²z`, `J₂₁ = -3x²`, `J₂₂ = -x³`.
     - Minors from Rows 1 and 2:
       - `M₀ = J₁₁ * J₂₂ - J₁₂ * J₂₁` (5 monomials)
       - `M₁ = J₁₀ * J₂₂ - J₁₂ * J₂₀` (5 monomials)
       - `M₂ = J₁₀ * J₂₁ - J₁₁ * J₂₀` (9 monomials)
     - Determinant: `Det = J₀₀ * M₀ - J₀₁ * M₁ + J₀₂ * M₂ = -2`.
     - Proved cleanly in < 1 second using Mathlib ring tactics, resolving the 1,600,000 heartbeat blowup in ProveIt.
   - Keller condition (Jacobian determinant is `-2 ≠ 0` in characteristic zero) and refutation
     of the Jacobian conjecture in dimension three and all dimensions over fields of characteristic zero.
2. **Selmer Trinomials** `S_n(X) = X^n - X - 1` (Ernst S. Selmer, 1956):
   - `selmer R n = X^n - X - 1`.
   - Monic of exact degree `n` and `natDegree n` for all `n ≥ 2`.
   - Irreducibility of `S_n` over `ℚ` for all `n ≠ 1` (in particular for all `n ≥ 2`).
   - Complete Abel-Ruffini Galois obstruction (Abel 1824, Ruffini 1799, Selmer 1956):
     for all `n ≥ 5`, `Gal(S_n/ℚ)` surjects onto the non-solvable symmetric group `S_n`
     (disclosing that `n ≥ 5` is required as `S_n` is solvable for `n ≤ 4`),
     and no complex root of `S_n` is solvable by radicals over `ℚ`.
-/

set_option linter.style.haveILetI false
set_option linter.missingDocs true
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true

noncomputable section

/-! ============================================================================
    1. ALPÖGE'S DIMENSION-3 POLYNOMIAL MAP & OPTIMIZED JACOBIAN DETERMINANT
   ============================================================================ -/

namespace VladMath.JacobianCounterexample

open Function Matrix MvPolynomial

universe u

/-- Index type `Fin 3` for coordinate variables of the 3-dimensional polynomial map. -/
abbrev I := Fin 3

variable {R : Type u} [CommRing R]

/-- Coordinate variable `X 0` representing `x`. -/
def x : MvPolynomial I R := X 0

/-- Coordinate variable `X 1` representing `y`. -/
def y : MvPolynomial I R := X 1

/-- Coordinate variable `X 2` representing `z`. -/
def z : MvPolynomial I R := X 2

/-- Coordinate polynomial `P` of Levent Alpöge's (2026) dimension-3 polynomial map:
    `P = (1 + xy)³ z + y²(1 + xy)(4 + 3xy)`. -/
def P : MvPolynomial I R :=
  (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

/-- Coordinate polynomial `Q` of Levent Alpöge's (2026) dimension-3 polynomial map:
    `Q = y + 3x(1 + xy)² z + 3xy²(4 + 3xy)`. -/
def Q : MvPolynomial I R :=
  y + 3 * x * (1 + x * y) ^ 2 * z + 3 * x * y ^ 2 * (4 + 3 * x * y)

/-- Coordinate polynomial `R` (denoted `W` to avoid clashing with the ring type `R`)
    of Levent Alpöge's (2026) dimension-3 polynomial map:
    `W = 2x - 3x²y - x³z`. -/
def W : MvPolynomial I R :=
  2 * x - 3 * x ^ 2 * y - x ^ 3 * z

/-- An alias for coordinate `W` matching the prompt's `R` notation. -/
def polyR : MvPolynomial I R := W

/-- An `n`-dimensional polynomial self-map over `R`. -/
abbrev PolynomialMap (n : Nat) (R : Type u) [CommSemiring R] :=
  Fin n → MvPolynomial (Fin n) R

namespace PolynomialMap

/-- Evaluate every coordinate polynomial of `f` at `a`. -/
def evalMap {n : Nat} {R : Type u} [CommSemiring R]
    (f : PolynomialMap n R) (a : Fin n → R) : Fin n → R :=
  fun i => MvPolynomial.eval a (f i)

/-- The formal Jacobian matrix, with coordinate polynomials as rows. -/
def jacobian {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  fun i j => pderiv j (f i)

/-- The formal Jacobian determinant. -/
def jacobianDet {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : MvPolynomial (Fin n) R :=
  (jacobian f).det

/-- The Keller condition: the formal Jacobian determinant is a nonzero constant polynomial. -/
def HasNonzeroConstantJacobian {n : Nat} {R : Type u} [CommRing R]
    (f : PolynomialMap n R) : Prop :=
  ∃ c : R, c ≠ 0 ∧ jacobianDet f = C c

/-- A polynomial two-sided inverse, stated by its induced action on points. -/
def HasPolynomialInverse {n : Nat} {R : Type u} [CommSemiring R]
    (f : PolynomialMap n R) : Prop :=
  ∃ g : PolynomialMap n R,
    LeftInverse (evalMap g) (evalMap f) ∧ RightInverse (evalMap g) (evalMap f)

end PolynomialMap

open PolynomialMap

/-- The Jacobian conjecture over `R` in a fixed dimension `n`. -/
def JacobianConjectureInDimension (n : Nat) (R : Type u) [Field R] : Prop :=
  ∀ f : PolynomialMap n R,
    HasNonzeroConstantJacobian f → HasPolynomialInverse f

/-- The Jacobian conjecture over `R` in all finite dimensions. -/
def JacobianConjecture (R : Type u) [Field R] : Prop :=
  ∀ n : Nat, JacobianConjectureInDimension n R

/-- Levent Alpöge's (2026) dimension-3 polynomial map `(P, Q, W)`. -/
def alpogeMap (R : Type u) [CommRing R] : PolynomialMap 3 R :=
  ![P, Q, W]

/-- Vanishing of partial derivatives on natural number literals. -/
theorem pderiv_ofNat {σ S : Type*} [CommSemiring S] {i : σ} (n : Nat) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ S) = 0 := by
  rw [← map_ofNat (C : S →+* MvPolynomial σ S) n]
  exact pderiv_C

/-! ### Explicit Entries of the Jacobian Matrix -/

/-- Jacobian entry `J₀₀ = ∂P/∂x`. -/
def J00 : MvPolynomial I R := 3 * y * (1 + x * y) ^ 2 * z + 7 * y ^ 3 + 6 * x * y ^ 4

/-- Jacobian entry `J₀₁ = ∂P/∂y`. -/
def J01 : MvPolynomial I R := 3 * x * (1 + x * y) ^ 2 * z + 8 * y + 21 * x * y ^ 2 + 12 * x ^ 2 * y ^ 3

/-- Jacobian entry `J₀₂ = ∂P/∂z`. -/
def J02 : MvPolynomial I R := (1 + x * y) ^ 3

/-- Jacobian entry `J₁₀ = ∂Q/∂x`. -/
def J10 : MvPolynomial I R := 3 * (1 + x * y) * (1 + 3 * x * y) * z + 12 * y ^ 2 + 18 * x * y ^ 3

/-- Jacobian entry `J₁₁ = ∂Q/∂y`. -/
def J11 : MvPolynomial I R := 1 + 6 * x ^ 2 * (1 + x * y) * z + 24 * x * y + 27 * x ^ 2 * y ^ 2

/-- Jacobian entry `J₁₂ = ∂Q/∂z`. -/
def J12 : MvPolynomial I R := 3 * x * (1 + x * y) ^ 2

/-- Jacobian entry `J₂₀ = ∂W/∂x` (Row 2, Column 0). -/
def J20 : MvPolynomial I R := 2 - 6 * x * y - 3 * x ^ 2 * z

/-- Jacobian entry `J₂₁ = ∂W/∂y` (Row 2, Column 1). -/
def J21 : MvPolynomial I R := -3 * x ^ 2

/-- Jacobian entry `J₂₂ = ∂W/∂z` (Row 2, Column 2). -/
def J22 : MvPolynomial I R := -x ^ 3

/-- Entry verification: `∂P/∂x` equals `J00`. -/
theorem J00_eq : pderiv (0 : I) (P : MvPolynomial I R) = J00 := by
  dsimp [P, x, y, z, J00]; simp [pderiv_ofNat]; ring

/-- Entry verification: `∂P/∂y` equals `J01`. -/
theorem J01_eq : pderiv (1 : I) (P : MvPolynomial I R) = J01 := by
  dsimp [P, x, y, z, J01]; simp [pderiv_ofNat]; ring

/-- Entry verification: `∂P/∂z` equals `J02`. -/
theorem J02_eq : pderiv (2 : I) (P : MvPolynomial I R) = J02 := by
  dsimp [P, x, y, z, J02]; simp [pderiv_ofNat]

/-- Entry verification: `∂Q/∂x` equals `J10`. -/
theorem J10_eq : pderiv (0 : I) (Q : MvPolynomial I R) = J10 := by
  dsimp [Q, x, y, z, J10]; simp [pderiv_ofNat]; ring

/-- Entry verification: `∂Q/∂y` equals `J11`. -/
theorem J11_eq : pderiv (1 : I) (Q : MvPolynomial I R) = J11 := by
  dsimp [Q, x, y, z, J11]; simp [pderiv_ofNat]; ring

/-- Entry verification: `∂Q/∂z` equals `J12`. -/
theorem J12_eq : pderiv (2 : I) (Q : MvPolynomial I R) = J12 := by
  dsimp [Q, x, y, z, J12]; simp [pderiv_ofNat]

/-- Entry verification: `∂W/∂x` equals `J20`. -/
theorem J20_eq : pderiv (0 : I) (W : MvPolynomial I R) = J20 := by
  dsimp [W, x, y, z, J20]; simp [pderiv_ofNat]; ring

/-- Entry verification: `∂W/∂y` equals `J21`. -/
theorem J21_eq : pderiv (1 : I) (W : MvPolynomial I R) = J21 := by
  dsimp [W, x, y, z, J21]; simp [pderiv_ofNat]

/-- Entry verification: `∂W/∂z` equals `J22`. -/
theorem J22_eq : pderiv (2 : I) (W : MvPolynomial I R) = J22 := by
  dsimp [W, x, y, z, J22]; simp [pderiv_ofNat]

/-! ### 2×2 Minor Factorization of Rows 1 and 2 for Laplace Expansion along Row 0 -/

/-- Minor `M₀ = J₁₁ * J₂₂ - J₁₂ * J₂₁` formed by rows 1, 2 and columns 1, 2. -/
def M0 : MvPolynomial I R := J11 * J22 - J12 * J21

/-- Minor `M₁ = J₁₀ * J₂₂ - J₁₂ * J₂₀` formed by rows 1, 2 and columns 0, 2. -/
def M1 : MvPolynomial I R := J10 * J22 - J12 * J20

/-- Minor `M₂ = J₁₀ * J₂₁ - J₁₁ * J₂₀` formed by rows 1, 2 and columns 0, 1. -/
def M2 : MvPolynomial I R := J10 * J21 - J11 * J20

/-- Minor `M₀` expands to exactly 5 monomials. -/
theorem M0_eq_five_monomials :
    (M0 : MvPolynomial I R) =
      8 * x ^ 3 - 6 * x ^ 4 * y - 18 * x ^ 5 * y ^ 2 - 6 * x ^ 5 * z - 6 * x ^ 6 * y * z := by
  dsimp [M0, J11, J22, J12, J21, x, y, z]; ring

/-- Minor `M₁` expands to exactly 5 monomials. -/
theorem M1_eq_five_monomials :
    (M1 : MvPolynomial I R) =
      -6 * x + 6 * x ^ 2 * y + 18 * x ^ 3 * y ^ 2 + 6 * x ^ 3 * z + 6 * x ^ 4 * y * z := by
  dsimp [M1, J10, J22, J12, J20, x, y, z]; ring

/-- Minor `M₂` expands to exactly 9 monomials. -/
theorem M2_eq_nine_monomials :
    (M2 : MvPolynomial I R) =
      -2 - 42 * x * y + 54 * x ^ 2 * y ^ 2 + 108 * x ^ 3 * y ^ 3 -
      18 * x ^ 2 * z + 60 * x ^ 3 * y * z + 90 * x ^ 4 * y ^ 2 * z +
      18 * x ^ 4 * z ^ 2 + 18 * x ^ 5 * y * z ^ 2 := by
  dsimp [M2, J10, J21, J11, J20, x, y, z]; ring

/-- **Optimized Jacobian Determinant Calculation**:
    `Det = J₀₀ * M₀ - J₀₁ * M₁ + J₀₂ * M₂ = -2`.
    This algebraic certificate verifies the Jacobian determinant via Laplace expansion
    along Row 0 using the 2×2 minors from Rows 1 and 2 in < 1 second,
    completely bypassing the 1,600,000 heartbeat blowup in ProveIt. -/
theorem det_minor_factorization :
    (J00 * M0 - J01 * M1 + J02 * M2 : MvPolynomial I R) = -2 := by
  dsimp [J00, J01, J02, M0, M1, M2, J10, J11, J12, J20, J21, J22, x, y, z]
  ring

/-- The standard Laplace expansion formula for a 3×3 matrix along Row 0. -/
def det3 {R : Type u} [CommRing R] (A : Matrix I I R) : R :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
  A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
  A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

/-- Equivalence between Laplace expansion along Row 0 (`det3`) and Mathlib's `Matrix.det`. -/
theorem det3_eq_det {R : Type u} [CommRing R] (A : Matrix I I R) :
    det3 A = A.det := by
  rw [Matrix.det_fin_three]
  simp only [det3]
  ring

/-- Formal Jacobian determinant of `alpogeMap` computed via the 2×2 minor factorization of Rows 1 and 2. -/
theorem det3_jacobian_alpogeMap (R : Type u) [CommRing R] :
    det3 (jacobian (alpogeMap R)) = (-2 : MvPolynomial I R) := by
  change (pderiv 0 (alpogeMap R 0) * (pderiv 1 (alpogeMap R 1) * pderiv 2 (alpogeMap R 2) -
            pderiv 2 (alpogeMap R 1) * pderiv 1 (alpogeMap R 2)) -
          pderiv 1 (alpogeMap R 0) * (pderiv 0 (alpogeMap R 1) * pderiv 2 (alpogeMap R 2) -
            pderiv 2 (alpogeMap R 1) * pderiv 0 (alpogeMap R 2)) +
          pderiv 2 (alpogeMap R 0) * (pderiv 0 (alpogeMap R 1) * pderiv 1 (alpogeMap R 2) -
            pderiv 1 (alpogeMap R 1) * pderiv 0 (alpogeMap R 2))) = -2
  have h00 : pderiv 0 (alpogeMap R 0) = (J00 : MvPolynomial I R) := J00_eq
  have h01 : pderiv 1 (alpogeMap R 0) = (J01 : MvPolynomial I R) := J01_eq
  have h02 : pderiv 2 (alpogeMap R 0) = (J02 : MvPolynomial I R) := J02_eq
  have h10 : pderiv 0 (alpogeMap R 1) = (J10 : MvPolynomial I R) := J10_eq
  have h11 : pderiv 1 (alpogeMap R 1) = (J11 : MvPolynomial I R) := J11_eq
  have h12 : pderiv 2 (alpogeMap R 1) = (J12 : MvPolynomial I R) := J12_eq
  have h20 : pderiv 0 (alpogeMap R 2) = (J20 : MvPolynomial I R) := J20_eq
  have h21 : pderiv 1 (alpogeMap R 2) = (J21 : MvPolynomial I R) := J21_eq
  have h22 : pderiv 2 (alpogeMap R 2) = (J22 : MvPolynomial I R) := J22_eq
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  exact det_minor_factorization

/-- The formal Jacobian determinant of Alpöge's map is constant `-2`
    over any commutative ring `R` (Levent Alpöge 2026). -/
theorem jacobianDet_alpogeMap (R : Type u) [CommRing R] :
    jacobianDet (alpogeMap R) = C (-2 : R) := by
  calc
    jacobianDet (alpogeMap R) = det3 (jacobian (alpogeMap R)) :=
      (det3_eq_det _).symm
    _ = (-2 : MvPolynomial I R) := det3_jacobian_alpogeMap R
    _ = C (-2 : R) := by rw [map_neg, map_ofNat]

/-! ### The Collision and Non-Injectivity Proof -/

/-- First point in the collision: `(-1, 1, 5)`. -/
def collision₀ (R : Type u) [CommRing R] : I → R := ![-1, 1, 5]

/-- Second point in the collision: `(0, -2, -16)`. -/
def collision₁ (R : Type u) [CommRing R] : I → R := ![0, -2, -16]

/-- The common image under Alpöge's map: `(0, -2, 0)`. -/
def collisionValue (R : Type u) [CommRing R] : I → R := ![0, -2, 0]

/-- `alpogeMap` evaluated at `(-1, 1, 5)` yields `(0, -2, 0)`. -/
theorem collision₀_value (R : Type u) [CommRing R] :
    evalMap (alpogeMap R) (collision₀ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, alpogeMap, collision₀, collisionValue,
      Matrix.cons_val_two, P, Q, W, x, y, z]

/-- `alpogeMap` evaluated at `(0, -2, -16)` yields `(0, -2, 0)`. -/
theorem collision₁_value (R : Type u) [CommRing R] :
    evalMap (alpogeMap R) (collision₁ R) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [evalMap, alpogeMap, collision₁, collisionValue,
      Matrix.cons_val_two, P, Q, W, x, y, z]

/-- Points `(-1, 1, 5)` and `(0, -2, -16)` collide to the same image `(0, -2, 0)`. -/
theorem collision (R : Type u) [CommRing R] :
    evalMap (alpogeMap R) (collision₀ R) =
      evalMap (alpogeMap R) (collision₁ R) :=
  (collision₀_value R).trans (collision₁_value R).symm

/-- Points `(-1, 1, 5)` and `(0, -2, -16)` are distinct over every nontrivial ring. -/
theorem collision_points_distinct (R : Type u) [CommRing R] [Nontrivial R] :
    collision₀ R ≠ collision₁ R := by
  intro h
  have h₀ := congrFun h 0
  simp [collision₀, collision₁] at h₀

/-- **Non-Injectivity Theorem** (Levent Alpöge 2026):
    Alpöge's polynomial map is not injective over any nontrivial commutative ring `R`. -/
theorem alpogeMap_not_injective
    (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Injective (evalMap (alpogeMap R)) := by
  intro h
  exact collision_points_distinct R (h (collision R))

/-! ### Disproof of the Jacobian Conjecture -/

/-- In characteristic zero, `-2 ≠ 0`, so `alpogeMap` satisfies the Keller condition
    over any field `R` with `[CharZero R]` (Levent Alpöge 2026). -/
theorem alpogeMap_has_nonzero_constant_jacobian
    (R : Type u) [Field R] [CharZero R] :
    HasNonzeroConstantJacobian (alpogeMap R) := by
  refine ⟨-2, by norm_num, ?_⟩
  exact jacobianDet_alpogeMap R

/-- Because `alpogeMap` has a collision, it cannot possess even a polynomial left inverse
    over any field `R`. -/
theorem alpogeMap_has_no_polynomial_inverse
    (R : Type u) [Field R] :
    ¬ HasPolynomialInverse (alpogeMap R) := by
  rintro ⟨g, hleft, _⟩
  exact alpogeMap_not_injective R hleft.injective

/-- **The Jacobian conjecture is false in dimension three** over every field of characteristic zero
    (disproved by Levent Alpöge 2026). -/
theorem jacobianConjectureInDimensionThree_false
    (R : Type u) [Field R] [CharZero R] :
    ¬ JacobianConjectureInDimension 3 R := by
  intro h
  exact alpogeMap_has_no_polynomial_inverse R
    (h (alpogeMap R) (alpogeMap_has_nonzero_constant_jacobian R))

/-- **The all-dimensions Jacobian conjecture is false** over every field of characteristic zero
    (disproved by Levent Alpöge 2026). -/
theorem jacobianConjecture_false
    (R : Type u) [Field R] [CharZero R] :
    ¬ JacobianConjecture R := by
  intro h
  exact jacobianConjectureInDimensionThree_false R (h 3)

/-- The classical complex Jacobian conjecture is false (disproved by Levent Alpöge 2026). -/
theorem jacobianConjecture_false_over_complex :
    ¬ JacobianConjecture ℂ :=
  jacobianConjecture_false ℂ

end VladMath.JacobianCounterexample

/-! ============================================================================
    2. THE SELMER TRINOMIAL: DEGREE, IRREDUCIBILITY, AND ABEL-RUFFINI OBSTRUCTION
   ============================================================================ -/

namespace VladMath.Selmer

open scoped NumberField Polynomial
open NumberField Polynomial

/-- The Selmer trinomial `S_n(X) = X^n - X - 1` (Ernst S. Selmer 1956). -/
def selmer (R : Type*) [Ring R] (n : ℕ) : R[X] := X ^ n - X - 1

/-- Notation alias `S_n` for the Selmer polynomial `selmer R n` (Ernst S. Selmer 1956). -/
@[nolint defsWithUnderscore]
abbrev S_n (R : Type*) [Ring R] (n : ℕ) : R[X] := selmer R n

/-- Ring homomorphism mapping property for Selmer polynomials: `(S_n).map φ = S_n`. -/
@[simp] lemma map_selmer {R K : Type*} [Ring R] [Ring K]
    (φ : R →+* K) (n : ℕ) : (selmer R n).map φ = selmer K n := by
  simp [selmer]

/-- The Selmer polynomial `S_n` is monic for all `n ≥ 2`. -/
@[simp] lemma selmer_monic {R : Type*} [Ring R] [Nontrivial R]
    {n : ℕ} (hn : 2 ≤ n) : (selmer R n).Monic := by
  rw [selmer, sub_sub]
  apply monic_X_pow_sub
  calc
    degree (X + 1 : R[X]) ≤ max (degree (X : R[X])) (degree (1 : R[X])) := degree_add_le _ _
    _ = 1 := by simp
    _ < n := by exact_mod_cast (show 1 < n by omega)

/-- The natural degree of `S_n` is `n` for all `n ≥ 2`. -/
lemma selmer_natDegree {R : Type*} [Ring R] [Nontrivial R]
    {n : ℕ} (hn : 2 ≤ n) : (selmer R n).natDegree = n := by
  rw [selmer, sub_sub]
  have hq : (X + 1 : R[X]).natDegree = 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa [hq] using (show 1 < n by omega)

/-- The degree of `S_n` is `n` for all `n ≥ 2`. -/
theorem selmer_degree {R : Type*} [Ring R] [Nontrivial R]
    {n : ℕ} (hn : 2 ≤ n) : (selmer R n).degree = n := by
  rw [degree_eq_natDegree (selmer_monic hn).ne_zero, selmer_natDegree hn]

/-- If `x` is a multiple root of `selmer K n`, it satisfies the linear relation `(n - 1) x + n = 0`. -/
lemma multiple_root_linear {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {x : K} (hx : 1 < (selmer K n).rootMultiplicity x) :
    ((n - 1 : ℕ) : K) * x + (n : K) = 0 := by
  have hp0 : selmer K n ≠ 0 := (selmer_monic hn).ne_zero
  obtain ⟨hx0, hx1⟩ := (one_lt_rootMultiplicity_iff_isRoot hp0).mp hx
  rw [IsRoot, selmer] at hx0
  rw [IsRoot, selmer, derivative_sub, derivative_sub, derivative_X_pow,
    derivative_X, derivative_one] at hx1
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, eval_C, sub_zero]
    at hx0 hx1
  have hxpow : x * x ^ (n - 1) = x ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have hx1mul : (n : K) * x ^ n - x = 0 := by
    calc
      (n : K) * x ^ n - x = (n : K) * (x * x ^ (n - 1)) - x := by rw [hxpow]
      _ = x * ((n : K) * x ^ (n - 1) - 1) := by ring
      _ = 0 := by rw [hx1, mul_zero]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  linear_combination -(n : K) * hx0 + hx1mul

/-- Distinct roots cannot both have multiplicity strictly greater than 1. -/
lemma multiple_roots_eq {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {x y : K} (hx : 1 < (selmer K n).rootMultiplicity x)
    (hy : 1 < (selmer K n).rootMultiplicity y) : x = y := by
  have hxlin := multiple_root_linear hn hx
  have hylin := multiple_root_linear hn hy
  have hn1 : ((n - 1 : ℕ) : K) ≠ 0 := by
    intro hn1
    have hncast : (n : K) = 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.cast_add, hn1, zero_add,
        Nat.cast_one]
    simp [hn1, hncast] at hxlin
  apply (mul_left_cancel₀ hn1)
  linear_combination hxlin - hylin

/-- Root multiplicity of any root of the Selmer polynomial is at most 2. -/
lemma rootMultiplicity_le_two {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (x : K) : (selmer K n).rootMultiplicity x ≤ 2 := by
  by_contra! hx
  have hp0 : selmer K n ≠ 0 := (selmer_monic hn).ne_zero
  have hxmult : 1 < (selmer K n).rootMultiplicity x := by omega
  obtain ⟨hx0, hx1⟩ := (one_lt_rootMultiplicity_iff_isRoot hp0).mp hxmult
  have hx0' := hx0
  have hx1' := hx1
  rw [IsRoot, selmer] at hx0'
  rw [IsRoot, selmer, derivative_sub, derivative_sub, derivative_X_pow,
    derivative_X, derivative_one] at hx1'
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, eval_C, sub_zero]
    at hx0' hx1'
  have hxn : (n : K) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_sub] at hx1'
    exact one_ne_zero (neg_eq_zero.mp hx1')
  have hxne : x ≠ 0 := by
    intro h
    subst x
    simp [show n ≠ 0 by omega] at hx0'
  have hn1 : ((n - 1 : ℕ) : K) ≠ 0 := by
    intro hn1
    have hncast : (n : K) = 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.cast_add, hn1, zero_add,
        Nat.cast_one]
    have hlin := multiple_root_linear hn hxmult
    simp [hn1, hncast] at hlin
  have hx2 := isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 2) hx
  rw [IsRoot, selmer, iterate_derivative_sub, iterate_derivative_sub,
    iterate_derivative_X_pow_eq_natCast_mul, iterate_derivative_X (by norm_num),
    iterate_derivative_one (by norm_num)] at hx2
  simp only [sub_zero, eval_mul, eval_natCast, eval_pow, eval_X] at hx2
  rw [Nat.cast_descFactorial_two] at hx2
  have hn1' : (n : K) - 1 ≠ 0 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ n)] using hn1
  exact (mul_ne_zero (mul_ne_zero hxn hn1') (pow_ne_zero _ hxne)) hx2

/-- Selmer polynomial with integer coefficients `selmer ℤ n`. -/
abbrev pZ (n : ℕ) : ℤ[X] := selmer ℤ n

/-- Selmer polynomial with rational coefficients `selmer ℚ n`. -/
abbrev pQ (n : ℕ) : ℚ[X] := selmer ℚ n

/-- Splitting field of the rational Selmer polynomial `pQ n` over `ℚ`. -/
abbrev splittingField (n : ℕ) := (pQ n).SplittingField

/-- **Selmer's Irreducibility Theorem** (Ernst S. Selmer 1956):
    The Selmer trinomial `X^n - X - 1` is irreducible over `ℚ` for all `n ≠ 1`
    (in particular for all `n ≥ 2`, as well as `n = 0`). -/
theorem pQ_irreducible {n : ℕ} (hn : n ≠ 1) : Irreducible (pQ n) := by
  simpa [pQ, selmer] using
    (Polynomial.X_pow_sub_X_sub_one_irreducible_rat (n := n) hn)

/-- Irreducibility theorem stated directly for `S_n(X) = selmer ℚ n` with hypothesis `2 ≤ n`
    (Ernst S. Selmer 1956). -/
theorem selmer_rat_irreducible {n : ℕ} (hn : 2 ≤ n) : Irreducible (selmer ℚ n) :=
  pQ_irreducible (by omega)

/-- Number field instance for the splitting field of `pQ n`. -/
instance splittingField_numberField (n : ℕ) : NumberField (splittingField n) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- The Selmer polynomial has exactly `n` splitting-field roots. -/
theorem pQ_rootSet_splittingField_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card ((pQ n).rootSet (splittingField n)) = n := by
  classical
  change Fintype.card ((pQ n).rootSet ((pQ n).SplittingField)) = n
  have hirr := pQ_irreducible (n := n) (by omega)
  exact (card_rootSet_eq_natDegree hirr.separable
    (SplittingField.splits (pQ n))).trans (selmer_natDegree (R := ℚ) hn)

/-- Base change of integer Selmer polynomial to rationals: `(pZ n).map (algebraMap ℤ ℚ) = pQ n`. -/
lemma pZ_map_rat (n : ℕ) :
    (pZ n).map (algebraMap ℤ ℚ) = pQ n := by
  simp [pZ, pQ, selmer]

/-- Rational base change identity for the Selmer polynomial in the splitting field. -/
lemma pZ_map_splittingField_eq (n : ℕ) :
    (pZ n).map (algebraMap ℤ (splittingField n)) =
      (pQ n).map (algebraMap ℚ (splittingField n)) := by
  have hrat := congrArg
    (fun q : ℚ[X] => q.map (algebraMap ℚ (splittingField n))) (pZ_map_rat n)
  rwa [map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ (splittingField n)] at hrat

/-- The integral and rational Selmer models define the same roots in the splitting field. -/
lemma pZ_rootSet_splittingField_eq (n : ℕ) :
    (pZ n).rootSet (splittingField n) =
      (pQ n).rootSet (splittingField n) := by
  classical
  rw [rootSet_def, rootSet_def, aroots, aroots, pZ_map_splittingField_eq n]

/-- The integral Selmer polynomial splits over the ring of integers `𝓞 (splittingField n)`. -/
lemma pZ_splits_ringOfIntegers {n : ℕ} (hn : 2 ≤ n) :
    ((pZ n).map (algebraMap ℤ (𝓞 (splittingField n)))).Splits := by
  let i : (𝓞 (splittingField n)) →+* splittingField n := algebraMap _ _
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := i) (FaithfulSMul.algebraMap_injective _ _)
  · have hrat := pZ_map_splittingField_eq n
    have hgoal :
        ((pZ n).map (algebraMap ℤ (𝓞 (splittingField n)))).map i =
          (pQ n).map (algebraMap ℚ (splittingField n)) := by
      dsimp [i]
      have hcomp :
          (algebraMap (𝓞 (splittingField n)) (splittingField n)).comp
              (Int.castRingHom (𝓞 (splittingField n))) =
            algebraMap ℤ (splittingField n) :=
        (IsScalarTower.algebraMap_eq ℤ (𝓞 (splittingField n)) (splittingField n)).symm
      rw [map_map, hcomp]
      exact hrat
    rw [hgoal]
    exact SplittingField.splits (pQ n)
  · intro a ha
    have ha' : a ∈ (pZ n).aroots (splittingField n) := by
      simpa [Polynomial.aroots, i, pZ, selmer] using ha
    exact ⟨⟨a, roots_mem_integralClosure
      (selmer_monic (R := ℤ) hn) ha'⟩, rfl⟩

/-- Bound on multiset cardinality when at most one element is duplicated with multiplicity at most 2. -/
lemma Multiset.card_le_toFinset_card_add_one {α : Type*} [DecidableEq α]
    (s : Multiset α)
    (hunique : ∀ ⦃x y⦄, 1 < s.count x → 1 < s.count y → x = y)
    (hatMostTwo : ∀ x, s.count x ≤ 2) :
    s.card ≤ s.toFinset.card + 1 := by
  by_cases hs : s.Nodup
  · rw [s.toFinset_card_of_nodup hs]
    omega
  · rw [Multiset.nodup_iff_count_le_one] at hs
    simp only [not_forall, not_le] at hs
    obtain ⟨x, hx⟩ := hs
    have hxmem : x ∈ s := Multiset.count_pos.mp (by omega)
    have herase : (s.erase x).Nodup := by
      rw [Multiset.nodup_iff_count_le_one]
      intro y
      by_cases hyx : y = x
      · subst y
        rw [Multiset.count_erase_self]
        have := hatMostTwo x
        omega
      · rw [Multiset.count_erase_of_ne hyx]
        by_contra! hy
        exact hyx (hunique hy hx)
    have hxmemerase : x ∈ s.erase x := by
      rw [← Multiset.count_pos, Multiset.count_erase_self]
      omega
    have hfin : (s.erase x).toFinset = s.toFinset := by
      ext y
      simp only [Multiset.mem_toFinset]
      by_cases hyx : y = x
      · subst y
        exact iff_of_true hxmemerase hxmem
      · exact Multiset.mem_erase_of_ne hyx
    rw [← hfin, Multiset.toFinset_card_of_nodup herase,
      Multiset.card_erase_add_one hxmem]

/-- Upper bound on polynomial degree by the cardinality of the root set plus 1 when `selmer K n` splits. -/
theorem selmer_natDegree_le_ncard_rootSet_add_one {K : Type*} [Field K]
    {n : ℕ} (hn : 2 ≤ n) (hsplit : (selmer K n).Splits) :
    (selmer K n).natDegree ≤ ((selmer K n).rootSet K).ncard + 1 := by
  classical
  let f := selmer K n
  have hcard : f.roots.card ≤ f.roots.toFinset.card + 1 :=
    Multiset.card_le_toFinset_card_add_one f.roots
      (fun {x y} hx hy => multiple_roots_eq (K := K) (n := n) hn
        (by simpa [f, count_roots] using hx)
        (by simpa [f, count_roots] using hy))
      (fun x => by simpa [f, count_roots] using
        rootMultiplicity_le_two (K := K) (n := n) hn x)
  rw [hsplit.natDegree_eq_card_roots]
  simpa [f, rootSet_def, aroots_def] using hcard

/-- Upper bound on Selmer degree by root set size plus 1 under base change to a splitting field `K`. -/
theorem selmer_natDegree_le_ncard_rootSet_add_one_of_splits_map
    {R K : Type*} [CommRing R] [Nontrivial R] [Field K] [Algebra R K]
    {n : ℕ} (hn : 2 ≤ n)
    (hsplit : ((selmer R n).map (algebraMap R K)).Splits) :
    (selmer R n).natDegree ≤ ((selmer R n).rootSet K).ncard + 1 := by
  have hsplitK : (selmer K n).Splits := by simpa using hsplit
  have h := selmer_natDegree_le_ncard_rootSet_add_one (K := K) hn hsplitK
  have hroot : (selmer R n).rootSet K = (selmer K n).rootSet K := by
    classical
    rw [rootSet_def, rootSet_def, aroots_def, aroots_def, map_selmer,
      Algebra.algebraMap_self, map_id]
  rw [selmer_natDegree hn]
  rw [selmer_natDegree hn] at h
  rwa [hroot]

/-- Exact cardinality `n` of the roots of `pZ n` in the ring of integers `𝓞 (splittingField n)`. -/
lemma pZ_rootSet_ringOfIntegers_ncard {n : ℕ} (hn : 2 ≤ n) :
    ((pZ n).rootSet (𝓞 (splittingField n))).ncard = n := by
  classical
  have hsplitsO := pZ_splits_ringOfIntegers hn
  have himage := hsplitsO.image_rootSet_algebraMap
    (B := splittingField n)
  have hroots := pZ_rootSet_splittingField_eq n
  have hcardQ := pQ_rootSet_splittingField_card hn
  calc
    ((pZ n).rootSet (𝓞 (splittingField n))).ncard =
        ((algebraMap (𝓞 (splittingField n)) (splittingField n)) ''
          (pZ n).rootSet (𝓞 (splittingField n))).ncard :=
      (Set.ncard_image_of_injective _
        (FaithfulSMul.algebraMap_injective (𝓞 (splittingField n))
          (splittingField n))).symm
    _ = ((pZ n).rootSet (splittingField n)).ncard := by rw [himage]
    _ = ((pQ n).rootSet (splittingField n)).ncard := by rw [hroots]
    _ = n := by rw [← Set.fintypeCard_eq_ncard, hcardQ]

/-- The supremum of inertia subgroups across all maximal ideals of `𝓞 L` is the full Galois group `⊤`. -/
theorem iSup_inertia_eq_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] :
    (⨆ m : MaximalSpectrum (𝓞 L), m.asIdeal.inertia Gal(L/ℚ)) = ⊤ := by
  classical
  let G := Gal(L/ℚ)
  haveI : IsGaloisGroup G ℚ L := by
    dsimp [G]
    exact IsGaloisGroup.of_isGalois ℚ L
  haveI : IsGaloisGroup G ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G ℤ (𝓞 L) ℚ L
  let H : Subgroup G :=
    ⨆ m : MaximalSpectrum (𝓞 L), m.asIdeal.inertia G
  change H = ⊤
  by_contra hH
  let F : IntermediateField ℚ L := FixedPoints.intermediateField H
  letI : Module ℚ F := Algebra.toModule
  haveI : IsGaloisGroup H F L := IsGaloisGroup.subgroup G ℚ L H
  haveI : IsGaloisGroup H (𝓞 F) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 L) F L
  have hF : Module.finrank ℚ F ≠ 1 := by
    intro h
    have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h
    have hFbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [IntermediateField.mem_bot]
      obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
      refine ⟨a, ?_⟩
      have ha' := congrArg (algebraMap F L) ha
      simpa only [IsScalarTower.algebraMap_apply ℚ F L,
        IntermediateField.algebraMap_apply] using ha'
    have hfixed :
         FixedPoints.intermediateField H = (⊥ : IntermediateField ℚ L) := by
      simpa only [F] using hFbot
    apply hH
    rw [← IsGaloisGroup.fixingSubgroup_fixedPoints G ℚ L H, hfixed,
      IsGaloisGroup.fixingSubgroup_bot]
  obtain ⟨q, hqmax, hqram⟩ :=
    NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hF
  have : q.IsMaximal := hqmax
  have : q.IsPrime := hqmax.isPrime
  obtain ⟨P, hPmax, hPq⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) q
  have : P.IsMaximal := hPmax
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver q := hPq
  have : Module.Finite ℤ (𝓞 L) :=
    IsIntegralClosure.finite ℤ ℚ L (𝓞 L)
  have : Module.Finite (𝓞 F) (𝓞 L) :=
    IsIntegralClosure.finite (𝓞 F) F L (𝓞 L)
  have hIP : P.inertia G ≤ H := by
    exact le_iSup
      (fun m : MaximalSpectrum (𝓞 L) => m.asIdeal.inertia G) ⟨P, hPmax⟩
  have hcard : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
    calc
      Nat.card (P.inertia H) =
          Nat.card ((P.inertia H).map H.subtype) :=
        (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ = Nat.card (P.inertia G) := by
        rw [AddSubgroup.inertia_map_subtype, inf_eq_left.mpr hIP]
  have hGcard : Nat.card (P.inertia G) = P.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G]
  have hHcard : Nat.card (P.inertia H) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) q P,
      Ideal.ramificationIdxIn_eq_ramificationIdx q P H]
  have hram : P.ramificationIdx ℤ = P.ramificationIdx (𝓞 F) :=
    hGcard.symm.trans (hcard.symm.trans hHcard)
  have hqidx : q.ramificationIdx ℤ = 1 := by
    apply (right_eq_mul₀ (P.ramificationIdx_pos (𝓞 F)).ne').mp
    exact hram.symm.trans (Ideal.ramificationIdx_tower (R := ℤ) q P)
  have hqunram : Algebra.IsUnramifiedAt ℤ q :=
    Ideal.ramificationIdx_eq_one_iff.mp hqidx
  exact hqram hqunram

/-- The splitting field of `pQ n` is a Galois extension of `ℚ`. -/
theorem splittingField_isGalois {n : ℕ} (hn : 2 ≤ n) :
    IsGalois ℚ (splittingField n) := by
  change IsGalois ℚ (pQ n).SplittingField
  letI : IsSplittingField ℚ (pQ n).SplittingField (pQ n) :=
    Polynomial.IsSplittingField.splittingField (pQ n)
  have hirr := pQ_irreducible (n := n) (by omega)
  exact IsGalois.of_separable_splitting_field hirr.separable

/-- Transitivity of the Galois action on the roots of `pZ n` in the ring of integers `𝓞 (splittingField n)`. -/
theorem pZ_rootSet_isPretransitive {n : ℕ} (hn : 2 ≤ n) :
    MulAction.IsPretransitive (pQ n).Gal
      ((pZ n).rootSet (𝓞 (splittingField n))) := by
  classical
  letI : IsGalois ℚ (splittingField n) := splittingField_isGalois hn
  have hsplitsO := pZ_splits_ringOfIntegers hn
  have himage := hsplitsO.image_rootSet_algebraMap
    (B := splittingField n)
  have hroots := pZ_rootSet_splittingField_eq n
  have hmaps :
      (algebraMap (𝓞 (splittingField n)) (splittingField n)) ''
          (pZ n).rootSet (𝓞 (splittingField n)) =
        (pQ n).rootSet (splittingField n) := himage.trans hroots
  have hirr := pQ_irreducible (n := n) (by omega)
  constructor
  intro x y
  let xL : (pQ n).rootSet (splittingField n) :=
    ⟨algebraMap (𝓞 (splittingField n)) (splittingField n) x,
      hmaps ▸ ⟨x, x.2, rfl⟩⟩
  let yL : (pQ n).rootSet (splittingField n) :=
    ⟨algebraMap (𝓞 (splittingField n)) (splittingField n) y,
      hmaps ▸ ⟨y, y.2, rfl⟩⟩
  have hx := minpoly.eq_of_irreducible hirr (mem_rootSet.mp xL.2).2
  have hy := minpoly.eq_of_irreducible hirr (mem_rootSet.mp yL.2).2
  obtain ⟨g, hg⟩ :=
    (Normal.minpoly_eq_iff_mem_orbit (splittingField n)).mp (hy.symm.trans hx)
  refine ⟨g, Subtype.ext ?_⟩
  apply (FaithfulSMul.algebraMap_injective
    (𝓞 (splittingField n)) (splittingField n))
  change g • (algebraMap (𝓞 (splittingField n)) (splittingField n) x) =
    algebraMap (𝓞 (splittingField n)) (splittingField n) y at hg
  change g • (algebraMap (𝓞 (splittingField n)) (splittingField n) x) =
    algebraMap (𝓞 (splittingField n)) (splittingField n) y
  exact hg

set_option backward.isDefEq.respectTransparency false in
/-- **Non-Solvability of the Selmer Galois Group** (Ernst S. Selmer 1956):
    For every degree `n ≥ 5`, `Gal(S_n/ℚ)` acts transitively on the roots in `𝓞 (splittingField n)`
    and surjects onto the full symmetric group `Equiv.Perm`, which is not solvable.
    Conditionality disclosure: the hypothesis `5 ≤ n` is strictly required,
    as the symmetric groups `S_n` are solvable for all degrees `n ≤ 4`. -/
theorem pQ_gal_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬ Group.IsSolvable (pQ n).Gal := by
  classical
  have hn2 : 2 ≤ n := by omega
  letI : IsGalois ℚ (splittingField n) := splittingField_isGalois hn2
  letI : MulAction.IsPretransitive (pQ n).Gal
      ((pZ n).rootSet (𝓞 (splittingField n))) :=
    pZ_rootSet_isPretransitive hn2
  have hmorse : ∀ m : MaximalSpectrum (𝓞 (splittingField n)),
      ((pZ n).rootSet (𝓞 (splittingField n))).ncard ≤
        ((pZ n).rootSet ((𝓞 (splittingField n)) ⧸ m.asIdeal)).ncard + 1 := by
    intro m
    let k := (𝓞 (splittingField n)) ⧸ m.asIdeal
    letI : Field k := Ideal.Quotient.field m.asIdeal
    let π : (𝓞 (splittingField n)) →ₐ[ℤ] k :=
      Ideal.Quotient.mkₐ ℤ m.asIdeal
    have hsplits : ((selmer ℤ n).map (algebraMap ℤ k)).Splits := by
      change ((pZ n).map (algebraMap ℤ k)).Splits
      exact (pZ_splits_ringOfIntegers hn2).of_algHom π
    have hbound := selmer_natDegree_le_ncard_rootSet_add_one_of_splits_map
      (R := ℤ) (K := k) (n := n) hn2 hsplits
    rw [pZ_rootSet_ringOfIntegers_ncard hn2]
    simpa only [pZ, selmer_natDegree (R := ℤ) hn2] using hbound
  have hsurj : Function.Surjective
      (MulAction.toPermHom (pQ n).Gal
        ((pZ n).rootSet (𝓞 (splittingField n)))) :=
    (pZ_splits_ringOfIntegers hn2).surjective_toPermHom_of_iSup_inertia_eq_top
      hmorse (iSup_inertia_eq_top (splittingField n))
  intro hsolv
  letI : Group.IsSolvable (pQ n).Gal := hsolv
  have hperm : Group.IsSolvable
      (Equiv.Perm ((pZ n).rootSet (𝓞 (splittingField n)))) :=
    Group.isSolvable_of_surjective hsurj
  have hcard : Fintype.card
      ((pZ n).rootSet (𝓞 (splittingField n))) = n := by
    rw [Set.fintypeCard_eq_ncard, pZ_rootSet_ringOfIntegers_ncard hn2]
  have hfive : 5 ≤ Cardinal.mk
      ((pZ n).rootSet (𝓞 (splittingField n))) := by
    rw [Cardinal.mk_fintype, hcard]
    exact_mod_cast hn
  exact (Equiv.Perm.not_isSolvable
    ((pZ n).rootSet (𝓞 (splittingField n))) hfive) hperm

/-- **Abel-Ruffini Obstruction for Selmer Trinomial Roots** (Abel 1824, Ruffini 1799, Selmer 1956):
    For every degree `n ≥ 5`, no complex root of the Selmer trinomial `X^n - X - 1`
    is solvable by radicals over `ℚ`.
    Conditionality disclosure: requires `5 ≤ n`. -/
theorem every_complex_root_not_solvableByRad (n : ℕ) (hn : 5 ≤ n)
    {x : ℂ} (hx : x ∈ (pQ n).rootSet ℂ) :
    x ∉ solvableByRad ℚ ℂ := by
  intro hxrad
  apply pQ_gal_not_solvable n hn
  have hirr := pQ_irreducible (n := n) (by omega)
  exact isSolvable_gal_of_irreducible hxrad hirr
    (Polynomial.aeval_eq_zero_of_mem_rootSet hx)

/-- The rational Selmer polynomial has exactly its degree many complex roots. -/
theorem pQ_rootSet_complex_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card ((pQ n).rootSet ℂ) = n := by
  classical
  have hirr := pQ_irreducible (n := n) (by omega)
  exact (card_rootSet_eq_natDegree hirr.separable
    (IsAlgClosed.splits ((pQ n).map (algebraMap ℚ ℂ)))).trans
      (selmer_natDegree (R := ℚ) hn)

/-- **Complete Selmer Obstruction Package** (Selmer 1956, Abel 1824, Ruffini 1799):
    For every degree `n ≥ 5`, the Selmer polynomial `X^n - X - 1` is monic of degree `n`,
    irreducible, has `n` distinct complex roots, its Galois group is not solvable,
    and NO complex root is solvable by radicals over `ℚ`.
    Conditionality disclosure: non-solvability requires `5 ≤ n`. -/
theorem selmer_all_complex_roots (n : ℕ) (hn : 5 ≤ n) :
    (pQ n).Monic ∧
      (pQ n).natDegree = n ∧
      Fintype.card ((pQ n).rootSet ℂ) = n ∧
      ¬ Group.IsSolvable (pQ n).Gal ∧
      ∀ x : ℂ, x ∈ (pQ n).rootSet ℂ → x ∉ solvableByRad ℚ ℂ := by
  have hn2 : 2 ≤ n := by omega
  exact ⟨selmer_monic (R := ℚ) hn2, selmer_natDegree (R := ℚ) hn2,
    pQ_rootSet_complex_card hn2, pQ_gal_not_solvable n hn,
    fun _ hx => every_complex_root_not_solvableByRad n hn hx⟩

end VladMath.Selmer

