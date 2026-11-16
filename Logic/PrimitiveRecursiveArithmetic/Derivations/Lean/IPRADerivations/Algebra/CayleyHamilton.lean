import IPRADerivations.Core.LinearAlgebra

/-!
# Cayley–Hamilton and the adjugate (`docs/proofs/algebra/cayley_hamilton_ipra`)

Derivations in `Prf PRAAx`, for integer matrices whose entries are free
variables, of:

* Cayley–Hamilton for `2 × 2` matrices, `A² − (tr A) A + (det A) I = 0`
  (`sections/core.tex`);
* Cayley–Hamilton for `3 × 3` matrices, `A³ − (tr A) A² + (tr adj A) A − (det A) I = 0`,
  where `tr adj A` is the sum of the principal `2 × 2` minors;
* the adjugate identity `M · adj M = (det M) I` (`core.tex`), as a schema: one iPRA
  theorem for every size `k`;
* multiplicativity of the determinant, `det (M N) = det M · det N`, for every size `k`;
* the quaternion identity `L(q r) = L(q) L(r)` for the left-multiplication matrices
  (`sections/applications.tex`), and Euler's four-square identity, the norm form of it.

Determinants and adjugates are the explicit iPRA terms of `Mat.det` (Laplace
expansion) and `Mat.adj` (cofactors).
-/

namespace LeanProofs.IPRA.Algebra.CayleyHamilton

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

/-! ## Variable matrices -/

private theorem idx_lt (k : ℕ) (i j : Fin k) : 2 * (k * i + j) + 1 < 2 * (k * k) := by
  have h₁ : k * (i : ℕ) + j < k * k :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _)
      (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ i.isLt)
  omega

/-- The `k × k` integer matrix whose entry `(i, j)` is the integer variable
number `k i + j`, read from `2 (k i + j)` and `2 (k i + j) + 1`. -/
def matVar (k : ℕ) : Mat k (2 * (k * k)) := fun i j =>
  ZT.var2 ⟨2 * (k * i + j), by have := idx_lt k i j; omega⟩
    ⟨2 * (k * i + j) + 1, by have := idx_lt k i j; omega⟩

/-- `matVar` shifted by `off` natural-number variables. -/
def matVarAt (k off : ℕ) : Mat k (off + 2 * (k * k)) := fun i j =>
  ZT.var2 ⟨off + 2 * (k * i + j), by have := idx_lt k i j; omega⟩
    ⟨off + 2 * (k * i + j) + 1, by have := idx_lt k i j; omega⟩

/-! ## The adjugate and determinant identities for every size -/

/-- `M · adj M = (det M) I` for every `k × k` integer matrix `M`. -/
def adjugateFormula (k : ℕ) : Fm PTm (2 * (k * k)) :=
  Mat.eqFm (Mat.mul (matVar k) (Mat.adj (matVar k))) (Mat.smul (Mat.det (matVar k)) Mat.one)

theorem mul_adjugate (k : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ (adjugateFormula k) :=
  closeUniv _ (Mat.derive (by simp [Matrix.mul_adjugate]))

/-- `det (M N) = det M · det N` for `k × k` integer matrices `M`, `N` with
independent variable entries. -/
def detMulFormula (k : ℕ) : Fm PTm (2 * (k * k) + 2 * (k * k)) :=
  let M : Mat k (2 * (k * k) + 2 * (k * k)) := fun i j =>
    ZT.var2 ⟨2 * (k * i + j), by have := idx_lt k i j; omega⟩
      ⟨2 * (k * i + j) + 1, by have := idx_lt k i j; omega⟩
  let N := matVarAt k (2 * (k * k))
  ZT.eq (Mat.det (Mat.mul M N)) (Mat.det M * Mat.det N)

theorem det_mul (k : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ (detMulFormula k) := by
  exact closeUniv _ <| ZT.derive (by simp [detMulFormula, Matrix.det_mul])

/-! ## Cayley–Hamilton in sizes 2 and 3 -/

private theorem ch2 {R : Type*} [CommRing R] (B : Matrix (Fin 2) (Fin 2) R) :
    B * B - B.trace • B + B.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- `A² − (tr A) A + (det A) I = 0` for `2 × 2` integer matrices. -/
def ch2Formula : Fm PTm (2 * (2 * 2)) :=
  let A := matVar 2
  Mat.eqFm (Mat.add (Mat.sub (Mat.mul A A) (Mat.smul (Mat.trace A) A))
    (Mat.smul (Mat.det A) Mat.one)) Mat.zero

theorem cayleyHamilton2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ ch2Formula :=
  closeUniv _ (Mat.derive (by simpa [ch2Formula] using ch2 _))

private theorem ch3 {R : Type*} [CommRing R] (B : Matrix (Fin 3) (Fin 3) R) :
    B * B * B - B.trace • (B * B) + B.adjugate.trace • B - B.det • (1 : Matrix (Fin 3) (Fin 3) R)
      = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three] <;> ring

/-- `A³ − (tr A) A² + (tr adj A) A − (det A) I = 0` for `3 × 3` integer matrices. -/
def ch3Formula : Fm PTm (2 * (3 * 3)) :=
  let A := matVar 3
  Mat.eqFm (Mat.sub (Mat.add (Mat.sub (Mat.mul (Mat.mul A A) A) (Mat.smul (Mat.trace A) (Mat.mul A A)))
      (Mat.smul (Mat.trace (Mat.adj A)) A)) (Mat.smul (Mat.det A) Mat.one)) Mat.zero

theorem cayleyHamilton3 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ ch3Formula :=
  closeUniv _ (Mat.derive (by simpa [ch3Formula] using ch3 _))

/-! ## Quaternions -/

section Quaternions

variable {m : ℕ}

/-- The product of quaternions `(a, b, c, d) = a + b i + c j + d k`. -/
def qmul (q r : Vec 4 m) : Vec 4 m :=
  ![q 0 * r 0 - q 1 * r 1 - q 2 * r 2 - q 3 * r 3,
    q 0 * r 1 + q 1 * r 0 + q 2 * r 3 - q 3 * r 2,
    q 0 * r 2 - q 1 * r 3 + q 2 * r 0 + q 3 * r 1,
    q 0 * r 3 + q 1 * r 2 - q 2 * r 1 + q 3 * r 0]

/-- The matrix of left multiplication by `q`. -/
def L (q : Vec 4 m) : Mat 4 m :=
  ![![q 0, -q 1, -q 2, -q 3],
    ![q 1, q 0, -q 3, q 2],
    ![q 2, q 3, q 0, -q 1],
    ![q 3, -q 2, q 1, q 0]]

/-- The quaternion norm `a² + b² + c² + d²`. -/
def qnorm (q : Vec 4 m) : ZT m := Vec.dot q q

abbrev q₁ : Vec 4 16 := ![.var2 0 1, .var2 2 3, .var2 4 5, .var2 6 7]
abbrev q₂ : Vec 4 16 := ![.var2 8 9, .var2 10 11, .var2 12 13, .var2 14 15]

/-- `L(q r) = L(q) L(r)`. -/
def leftMulFormula : Fm PTm 16 := Mat.eqFm (L (qmul q₁ q₂)) (Mat.mul (L q₁) (L q₂))

theorem leftMul_hom : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16 leftMulFormula := by
  refine closeUniv 16 (Mat.derive ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMulFormula, L, qmul, Mat.mul, Fin.sum_univ_four] <;> ring

/-- Euler's four-square identity `N(q) N(r) = N(q r)`. -/
def fourSquareFormula : Fm PTm 16 := ZT.eq (qnorm q₁ * qnorm q₂) (qnorm (qmul q₁ q₂))

theorem euler_four_squares : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16 fourSquareFormula :=
  closeUniv 16 (ZT.derive (by
    simp [fourSquareFormula, qnorm, qmul, dotProduct, Fin.sum_univ_four]; ring))

end Quaternions

end LeanProofs.IPRA.Algebra.CayleyHamilton
