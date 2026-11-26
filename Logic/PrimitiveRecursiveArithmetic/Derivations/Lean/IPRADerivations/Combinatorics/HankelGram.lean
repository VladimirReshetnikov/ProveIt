import Mathlib.LinearAlgebra.Matrix.Block
import IPRADerivations.Core.IntCancel
import IPRADerivations.Foundations.CofactorAnnihilator
import IPRADerivations.Combinatorics.CatalanSmallPrimes

/-!
# Hankel determinants from Gram factorizations (`catalan_numbers_ipra_2026-11-16`, Section 6)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Section "Hankel determinants and the
moment problem": `det[Cat_{i+j}] = 1`, `det[Cat_{i+j+1}] = 1` (6.1), `det[Cat_{i+j+2}] = n + 1`
(6.2). "`[Cat_{i+j}] = E^{(n)} (E^{(n)})ᵀ`, `[Cat_{i+j+1}] = O^{(n)} (O^{(n)})ᵀ` (6.7). Both
factors are unit lower triangular. Determinant multiplicativity and transpose invariance now
give (6.1)." For (6.2): "`[Cat_{r+s+2}] = M^{(n)} (M^{(n)})ᵀ` (6.8). Cauchy–Binet expresses its
determinant as the sum of the squares of the `n + 1` maximal minors of `M^{(n)}`." And the
characterization (6.10): "the newest term `a_{2r}` occurs only in the southeast corner. Its
cofactor is the preceding unshifted determinant, equal to `1`. Therefore the equation
'determinant `= 1`' ... uniquely determines `a_{2r}`."

The determinant arguments are derived for integer-term matrices of every size (a parameter of
the Lean statements), on `Core/LinearAlgebra`:

* `unit_gram_ring`, `unit_gram_det`: if `H = L Lᵀ` with `L` lower triangular with unit
  diagonal, then `det H = 1`: (6.1) from (6.7);
* `cb_ring`, `rowGram`, `cauchy_binet`: Cauchy–Binet for an `n × (n + 1)` matrix `M` (the rows
  `1, …, n` of a square matrix `N`): `det(M Mᵀ) = Σ_j (maximal minor j)²`, when that sum is
  not zero. The proof borders `M` with its own cofactor vector `λ`: the bordered matrix `N'`
  has `det N' = λ · λ` and `N' N'ᵀ = diag(λ · λ, M Mᵀ)`, so
  `(λ · λ) det(M Mᵀ) = (λ · λ)²`, and the nonzero factor is cancelled in the object theory
  (`Core/IntCancel`);
* `natLit_succ_ne`: a positive numeral is not zero (the nonvanishing needed for (6.2), where
  the sum of squares is `n + 1`);
* `corner_ring`, `corner_determines`: two matrices that agree outside the southeast corner,
  have equal determinants, and whose leading principal minor has determinant `1`, have equal
  corners: the step of the characterization (6.10);
* `hankel0`, `hankel1`, `hankel0_two`, `hankel1_two`, `hankel2_one`: the instances
  `det[Cat_{i+j}]_{2×2} = 1`, `det[Cat_{i+j+1}]_{2×2} = 1`, `det[Cat_2]_{1×1} = 2`, with the
  Catalan terms of `Combinatorics/Catalan`.

Not derived: the ballot Gram identities (6.5), (6.6), (6.8) and the unit maximal minors
(`lem:maximal-minors`) for a variable size, which are the hypotheses that turn `unit_gram_det`
and `cauchy_binet` into (6.1) and (6.2) for every `n`.
-/

namespace LeanProofs.IPRA.Combinatorics.HankelGram

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open LeanProofs.IPRA.Foundations.CofactorAnnihilator (cof toZ_cof row_adj_succ eval_ring)
open LeanProofs.IPRA.Combinatorics.Catalan
open LeanProofs.IPRA.Combinatorics.CatalanGrowth (cat_one)
open LeanProofs.IPRA.Combinatorics.CatalanSmallPrimes (cat_two cat_three)
open Syn Matrix
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- A Gram matrix of a unit lower triangular matrix has determinant `1`. -/
theorem unit_gram_ring (L : Matrix (Fin k) (Fin k) R) (hlow : ∀ i j, i < j → L i j = 0)
    (hdiag : ∀ i, L i i = 1) : (L * Lᵀ).det = 1 := by
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun i j h => hlow i j (by simpa using h))]
    simp [hdiag]
  rw [Matrix.det_mul, Matrix.det_transpose, hL, _root_.mul_one]

/-- Cauchy–Binet for `n × (n + 1)`, before cancellation: with `λ` the cofactor vector of the
rows `1, …, n`, `(λ · λ) det(M Mᵀ) = (λ · λ)²`. -/
theorem cb_ring (N : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    ((fun j => N.adjugate j 0) ⬝ᵥ fun j => N.adjugate j 0) *
        (Matrix.of fun i j : Fin k => N i.succ ⬝ᵥ N j.succ).det =
      ((fun j => N.adjugate j 0) ⬝ᵥ fun j => N.adjugate j 0) ^ 2 := by
  set lam : Fin (k + 1) → R := fun j => N.adjugate j 0 with hlam
  set N' := N.updateRow 0 lam with hN'
  have h1 : N'.det = lam ⬝ᵥ lam := (eval_ring N lam).symm
  have hrow0 : N' 0 = lam := Matrix.updateRow_self
  have hrow : ∀ i : Fin k, N' i.succ = N i.succ := fun i =>
    Matrix.updateRow_ne (Fin.succ_ne_zero i)
  have hA00 : (N' * N'ᵀ) 0 0 = lam ⬝ᵥ lam := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, hrow0]
  have hA0j : ∀ j : Fin k, (N' * N'ᵀ) 0 j.succ = 0 := fun j => by
    have h := row_adj_succ N j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow0, hrow]
    exact (Finset.sum_congr rfl fun l _ => _root_.mul_comm (lam l) (N j.succ l)).trans h
  have hsub : (N' * N'ᵀ).submatrix Fin.succ Fin.succ =
      Matrix.of fun i j : Fin k => N i.succ ⬝ᵥ N j.succ := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, dotProduct, hrow]
  have h2 : (N' * N'ᵀ).det =
      lam ⬝ᵥ lam * (Matrix.of fun i j : Fin k => N i.succ ⬝ᵥ N j.succ).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [hA00, hA0j, hsub]
  rw [← h2, Matrix.det_mul, Matrix.det_transpose, h1]
  ring

/-- The corner of a matrix is determined by the rest, the determinant, and a unit leading
minor. -/
theorem corner_ring {r : ℕ} (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hagree : ∀ i j, ¬(i = Fin.last r ∧ j = Fin.last r) → A i j = A' i j)
    (hdet : A.det = A'.det) (hminor : (A'.submatrix Fin.castSucc Fin.castSucc).det = 1) :
    A (Fin.last r) (Fin.last r) = A' (Fin.last r) (Fin.last r) := by
  have hA : A = A'.updateRow (Fin.last r)
      (A' (Fin.last r) + (A (Fin.last r) (Fin.last r) - A' (Fin.last r) (Fin.last r)) •
        Pi.single (Fin.last r) 1) := by
    ext i j
    by_cases hi : i = Fin.last r
    · rw [hi, Matrix.updateRow_self]
      by_cases hj : j = Fin.last r
      · rw [hj]
        simp
      · rw [hagree _ j (fun h => hj h.2)]
        simp [Pi.single_eq_of_ne hj]
    · rw [Matrix.updateRow_ne hi, hagree i j (fun h => hi h.1)]
  have hadj : A'.adjugate (Fin.last r) (Fin.last r) = 1 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, hminor,
      Even.neg_one_pow ⟨_, rfl⟩, _root_.one_mul]
  have hd : A.det = A'.det +
      (A (Fin.last r) (Fin.last r) - A' (Fin.last r) (Fin.last r)) := by
    conv_lhs => rw [hA]
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
      ← Matrix.adjugate_apply, hadj, _root_.mul_one]
  linear_combination hdet - hd

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- (6.1) from (6.7): a unit lower triangular Gram factorization gives determinant `1`. -/
theorem unit_gram_det {L H : Mat k n}
    (hlow : ∀ i j, i < j → (Γ ⊢[PRAAx] ZT.eq (L i j) (ZT.natLit 0)))
    (hdiag : ∀ i, Γ ⊢[PRAAx] ZT.eq (L i i) (ZT.natLit 1))
    (hH : Γ ⊢[PRAAx] Mat.eqFm H (Mat.mul L (Mat.transpose L))) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det H) (ZT.natLit 1) := by
  have e := Mat.toZ_eq hH
  rw [Mat.toZ_mul, Mat.toZ_transpose] at e
  refine ZT.derive ?_
  rw [Mat.toZ_det, e, ZT.toZ_natLit, Nat.cast_one]
  refine unit_gram_ring _ (fun i j h => ?_) (fun i => ?_)
  · simpa using ZT.toZ_eq (hlow i j h)
  · simpa using ZT.toZ_eq (hdiag i)

/-- The Gram matrix of the rows `1, …, k` of a `(k + 1) × (k + 1)` matrix. -/
def rowGram (N : Mat (k + 1) n) : Mat k n := fun i j => Vec.dot (N i.succ) (N j.succ)

theorem toZ_rowGram (N : Mat (k + 1) n) :
    Mat.toZ Γ (rowGram N) =
      Matrix.of fun i j : Fin k => (Mat.toZ Γ N) i.succ ⬝ᵥ (Mat.toZ Γ N) j.succ := by
  ext i j
  show ZT.toZ Γ (Vec.dot (N i.succ) (N j.succ)) = _
  rw [Vec.toZ_dot]
  rfl

/-- Cauchy–Binet for `k × (k + 1)`: `det(M Mᵀ)` is the sum of the squares of the maximal
minors, when that sum is not zero. -/
theorem cauchy_binet (N : Mat (k + 1) n)
    (hs : Γ ⊢[PRAAx] neg (ZT.eq (Vec.dot (cof N) (cof N)) (ZT.natLit 0))) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (rowGram N)) (Vec.dot (cof N) (cof N)) := by
  have h0 : Γ ⊢[PRAAx] ZT.eq (Vec.dot (cof N) (cof N) *
      (Mat.det (rowGram N) - Vec.dot (cof N) (cof N))) (ZT.natLit 0) :=
    ZT.derive (by
      rw [ZT.toZ_mul, ZT.toZ_sub, Mat.toZ_det, Vec.toZ_dot, toZ_cof, toZ_rowGram,
        ZT.toZ_natLit, Nat.cast_zero]
      have h := cb_ring (Mat.toZ Γ N)
      linear_combination h)
  have e := ZT.toZ_eq (zt_mul_cancel_left hs h0)
  rw [ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_zero] at e
  refine ZT.derive ?_
  linear_combination e

/-- A positive numeral is not zero. -/
theorem natLit_succ_ne (m : ℕ) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit (m + 1) : ZT n) (ZT.natLit 0)) := by
  refine .impI (succ_ne_zero' _ (a := num m) ?_)
  have h : (ZT.eq (ZT.natLit (m + 1) : ZT n) (ZT.natLit 0) :: Γ) ⊢[PRAAx]
      succ (num m) + zero ≐ zero + zero := Prf.hyp0
  exact (add_zero _).eqSymm.eqTrans (h.eqTrans (zero_add _))

/-- (6.10), the step: the southeast corner is determined. -/
theorem corner_determines {r : ℕ} {A A' : Mat (r + 1) n}
    (hagree : ∀ i j, ¬(i = Fin.last r ∧ j = Fin.last r) →
      (Γ ⊢[PRAAx] ZT.eq (A i j) (A' i j)))
    (hdet : Γ ⊢[PRAAx] ZT.eq (Mat.det A) (Mat.det A'))
    (hminor : Γ ⊢[PRAAx]
      ZT.eq (Mat.det (fun a b : Fin r => A' a.castSucc b.castSucc)) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (A (Fin.last r) (Fin.last r)) (A' (Fin.last r) (Fin.last r)) := by
  have ed := ZT.toZ_eq hdet
  have em := ZT.toZ_eq hminor
  rw [Mat.toZ_det, Mat.toZ_det] at ed
  rw [Mat.toZ_det, ZT.toZ_natLit, Nat.cast_one] at em
  refine ZT.derive ?_
  exact corner_ring (Mat.toZ Γ A) (Mat.toZ Γ A') (fun i j h => ZT.toZ_eq (hagree i j h)) ed em

/-! ## Small instances with the Catalan terms -/

/-- `[Cat_{i+j}]_{0 ≤ i, j < 2}`. -/
def hankel0 : Mat 2 n :=
  ![![ZT.ofNat (cat zero), ZT.ofNat (cat (succ zero))],
    ![ZT.ofNat (cat (succ zero)), ZT.ofNat (cat (succ (succ zero)))]]

/-- `[Cat_{i+j+1}]_{0 ≤ i, j < 2}`. -/
def hankel1 : Mat 2 n :=
  ![![ZT.ofNat (cat (succ zero)), ZT.ofNat (cat (succ (succ zero)))],
    ![ZT.ofNat (cat (succ (succ zero))), ZT.ofNat (cat (succ (succ (succ zero))))]]

/-- (6.1) for `n = 2`: `det[Cat_{i+j}] = 1`. -/
theorem hankel0_two : Γ ⊢[PRAAx] ZT.eq (Mat.det (hankel0 (n := n))) (ZT.natLit 1) := by
  have c0 := natEq (cat_zero (Γ := Γ) (n := n))
  have c1 := natEq (cat_one (Γ := Γ))
  have c2 := natEq (cat_two (Γ := Γ))
  refine ZT.derive ?_
  rw [Mat.toZ_det, Matrix.det_fin_two]
  simp only [Mat.toZ_apply, hankel0, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_one]
  ipra_simps
  linear_combination 𝔞 (cat (succ (succ zero))) * c0 + c2 - (𝔞 (cat (succ zero)) + 1) * c1

/-- (6.1) for `n = 2`: `det[Cat_{i+j+1}] = 1`. -/
theorem hankel1_two : Γ ⊢[PRAAx] ZT.eq (Mat.det (hankel1 (n := n))) (ZT.natLit 1) := by
  have c1 := natEq (cat_one (Γ := Γ))
  have c2 := natEq (cat_two (Γ := Γ))
  have c3 := natEq (cat_three (Γ := Γ))
  refine ZT.derive ?_
  rw [Mat.toZ_det, Matrix.det_fin_two]
  simp only [Mat.toZ_apply, hankel1, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_one]
  ipra_simps
  linear_combination 𝔞 (cat (succ (succ (succ zero)))) * c1 + c3 -
    (𝔞 (cat (succ (succ zero))) + 2) * c2

/-- (6.2) for `n = 1`: `det[Cat_2] = 2`. -/
theorem hankel2_one : Γ ⊢[PRAAx]
    ZT.eq (Mat.det (fun _ _ : Fin 1 => (ZT.ofNat (cat (succ (succ zero))) : ZT n)))
      (ZT.natLit 2) := by
  have c2 := natEq (cat_two (Γ := Γ))
  refine ZT.derive ?_
  rw [Mat.toZ_det, Matrix.det_fin_one]
  simp only [Mat.toZ_apply, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_ofNat]
  ipra_simps
  linear_combination c2

end LeanProofs.IPRA.Combinatorics.HankelGram
