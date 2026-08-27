import FabiusFunction.ThueMorseEnumerators
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic

/-!
# Hankel determinants of the period-doubling sequence

The mod-two engine behind the Allouche–Peyrière–Wen–Wen Hankel
rigidity theorem: **every Hankel determinant of the period-doubling
sequence over `𝔽₂` equals `1`**.

The period-doubling bit is `pd(k) = τ(k) + τ(k+1) (mod 2)` for the
Thue–Morse bit `τ`; it obeys `pd(2k) = 1`, `pd(2k+1) = 1 + pd(k)`.
Two families of determinants close under index halving: the Hankel
determinants `D(n)` of `pd` itself and the Hankel determinants `Y(n)`
of the half-index sequence `pd(⌊k/2⌋)`:

`D(2n) = D(n)`, `D(2n+1) = Y(n)`,
`Y(2n) = D(n)·Y(n)`, `Y(2n+1) = D(n+1)·Y(n)`,

whence everything is `1` by strong induction.  Each identity is a
parity interleaving of rows and columns followed by one or two
unitriangular eliminations — over `𝔽₂` all permutation signs vanish.

The block machinery (`det_fromBlocks_of_eq_mul`,
`det_fromBlocks_symm`, the interleaving equivalences) is stated over
an arbitrary commutative ring for reuse by the integer-level
Thue–Morse Hankel recursions.

This file proves the two `D`-halvings and the two `Y`-halvings; the
strong induction and the applications live in `ThueMorseHankel.lean`.
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

/-! ### Reusable block-determinant lemmas -/

/-- **Row reduction for block determinants**: if the lower-left block
is `X·A`, one unitriangular elimination gives
`det [[A,B],[C,D]] = det A · det (D - X·B)`. -/
theorem det_fromBlocks_of_eq_mul {R : Type*} [CommRing R]
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (A : Matrix p p R) (B : Matrix p q R) (C : Matrix q p R)
    (D : Matrix q q R) (X : Matrix q p R) (hC : C = X * A) :
    (fromBlocks A B C D).det = A.det * (D - X * B).det := by
  have hL : (fromBlocks (1 : Matrix p p R) (0 : Matrix p q R)
      (-X) (1 : Matrix q q R)).det = 1 := by
    rw [det_fromBlocks_zero₁₂, det_one, det_one, one_mul]
  calc (fromBlocks A B C D).det
      = ((fromBlocks (1 : Matrix p p R) (0 : Matrix p q R)
          (-X) (1 : Matrix q q R)) * fromBlocks A B C D).det := by
        rw [det_mul, hL, one_mul]
    _ = (fromBlocks A B 0 (D - X * B)).det := by
        rw [fromBlocks_multiply, Matrix.one_mul, Matrix.one_mul,
          Matrix.zero_mul, Matrix.zero_mul, add_zero, add_zero,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.one_mul,
          Matrix.one_mul, hC, neg_add_cancel, ← sub_eq_neg_add]
    _ = A.det * (D - X * B).det := det_fromBlocks_zero₂₁ _ _ _

/-- **The symmetric two-block determinant**:
`det [[P,Q],[Q,P]] = det (P+Q) · det (P-Q)`. -/
theorem det_fromBlocks_symm {R : Type*} [CommRing R]
    {p : Type*} [Fintype p] [DecidableEq p] (P Q : Matrix p p R) :
    (fromBlocks P Q Q P).det = (P + Q).det * (P - Q).det := by
  have hL : (fromBlocks (1 : Matrix p p R) (0 : Matrix p p R)
      (-(1 : Matrix p p R)) (1 : Matrix p p R)).det = 1 := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul]
  have hR : (fromBlocks (1 : Matrix p p R) (0 : Matrix p p R)
      (1 : Matrix p p R) (1 : Matrix p p R)).det = 1 := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul]
  calc (fromBlocks P Q Q P).det
      = ((fromBlocks (1 : Matrix p p R) (0 : Matrix p p R)
          (-(1 : Matrix p p R)) (1 : Matrix p p R)) *
          fromBlocks P Q Q P *
          fromBlocks (1 : Matrix p p R) (0 : Matrix p p R)
            (1 : Matrix p p R) (1 : Matrix p p R)).det := by
        rw [det_mul, det_mul, hL, hR, one_mul, mul_one]
    _ = (fromBlocks (P + Q) Q 0 (P - Q)).det := by
        rw [fromBlocks_multiply, fromBlocks_multiply]
        congr 1
        rw [Matrix.one_mul, Matrix.one_mul, Matrix.zero_mul,
          Matrix.zero_mul, add_zero, add_zero, Matrix.neg_mul,
          Matrix.neg_mul, Matrix.one_mul, Matrix.one_mul,
          Matrix.mul_one, Matrix.mul_one, Matrix.mul_zero, zero_add,
          Matrix.mul_one, Matrix.mul_one, Matrix.mul_zero, zero_add]
        congr 1
        · abel
        · abel
    _ = (P + Q).det * (P - Q).det := det_fromBlocks_zero₂₁ _ _ _

/-! ### Interleaving equivalences -/

/-- Even/odd interleaving of `Fin (2n)`. -/
def interleaveEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun := Sum.elim (fun i => ⟨2 * i, by omega⟩) fun i => ⟨2 * i + 1, by omega⟩
  invFun k :=
    if h : (k : ℕ) % 2 = 0 then Sum.inl ⟨k / 2, by omega⟩
    else Sum.inr ⟨k / 2, by omega⟩
  left_inv := by
    rintro (i | i) <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
    · rw [dif_pos (Nat.mul_mod_right 2 (i : ℕ))]
      exact congrArg Sum.inl
        (Fin.ext (show 2 * (i : ℕ) / 2 = (i : ℕ) by omega))
    · rw [dif_neg (show ¬(2 * (i : ℕ) + 1) % 2 = 0 by omega)]
      exact congrArg Sum.inr
        (Fin.ext (show (2 * (i : ℕ) + 1) / 2 = (i : ℕ) by omega))
  right_inv := by
    intro k
    dsimp only
    by_cases h : (k : ℕ) % 2 = 0
    · rw [dif_pos h]
      dsimp only [Sum.elim_inl]
      exact Fin.ext (show 2 * ((k : ℕ) / 2) = (k : ℕ) by omega)
    · rw [dif_neg h]
      dsimp only [Sum.elim_inr]
      exact Fin.ext (show 2 * ((k : ℕ) / 2) + 1 = (k : ℕ) by omega)

/-- Even/odd interleaving of `Fin (2n+1)`. -/
def interleaveOddEquiv (n : ℕ) : Fin (n + 1) ⊕ Fin n ≃ Fin (2 * n + 1) where
  toFun := Sum.elim (fun i => ⟨2 * i, by omega⟩) fun i => ⟨2 * i + 1, by omega⟩
  invFun k :=
    if h : (k : ℕ) % 2 = 0 then Sum.inl ⟨k / 2, by omega⟩
    else Sum.inr ⟨k / 2, by omega⟩
  left_inv := by
    rintro (i | i) <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
    · rw [dif_pos (Nat.mul_mod_right 2 (i : ℕ))]
      exact congrArg Sum.inl
        (Fin.ext (show 2 * (i : ℕ) / 2 = (i : ℕ) by omega))
    · rw [dif_neg (show ¬(2 * (i : ℕ) + 1) % 2 = 0 by omega)]
      exact congrArg Sum.inr
        (Fin.ext (show (2 * (i : ℕ) + 1) / 2 = (i : ℕ) by omega))
  right_inv := by
    intro k
    dsimp only
    by_cases h : (k : ℕ) % 2 = 0
    · rw [dif_pos h]
      dsimp only [Sum.elim_inl]
      exact Fin.ext (show 2 * ((k : ℕ) / 2) = (k : ℕ) by omega)
    · rw [dif_neg h]
      dsimp only [Sum.elim_inr]
      exact Fin.ext (show 2 * ((k : ℕ) / 2) + 1 = (k : ℕ) by omega)

@[simp] theorem interleaveEquiv_inl (n : ℕ) (i : Fin n) :
    ((interleaveEquiv n) (Sum.inl i) : ℕ) = 2 * i := rfl

@[simp] theorem interleaveEquiv_inr (n : ℕ) (i : Fin n) :
    ((interleaveEquiv n) (Sum.inr i) : ℕ) = 2 * i + 1 := rfl

@[simp] theorem interleaveOddEquiv_inl (n : ℕ) (i : Fin (n + 1)) :
    ((interleaveOddEquiv n) (Sum.inl i) : ℕ) = 2 * i := rfl

@[simp] theorem interleaveOddEquiv_inr (n : ℕ) (i : Fin n) :
    ((interleaveOddEquiv n) (Sum.inr i) : ℕ) = 2 * i + 1 := rfl

/-! ### The period-doubling bit -/

/-- The period-doubling bit `pd(k) = τ(k) + τ(k+1)` over `𝔽₂`. -/
def pdBit (k : ℕ) : ZMod 2 :=
  (thueMorseBit k : ZMod 2) + (thueMorseBit (k + 1) : ZMod 2)

theorem pdBit_two_mul (k : ℕ) : pdBit (2 * k) = 1 := by
  have h1 := thueMorseBit_two_mul k
  have h2 := thueMorseBit_two_mul_add_one k
  have hb := thueMorseBit_le_one k
  rw [pdBit, h1, h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h <;> rw [h] <;>
    decide
theorem pdBit_two_mul_add_one (k : ℕ) :
    pdBit (2 * k + 1) = 1 + pdBit k := by
  have h2 := thueMorseBit_two_mul_add_one k
  have h4 := thueMorseBit_two_mul (k + 1)
  have hb := thueMorseBit_le_one k
  rw [pdBit, pdBit, h2, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, h4]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h <;> rw [h] <;>
    generalize (thueMorseBit (k + 1) : ZMod 2) = c <;> revert c <;> decide

/-- The halving identity for adjacent sums:
`pd(k) + pd(k+1) = pd(⌊k/2⌋)`. -/
theorem pdBit_add_succ (k : ℕ) :
    pdBit k + pdBit (k + 1) = pdBit (k / 2) := by
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    rw [show t + t = 2 * t by ring, pdBit_two_mul,
      pdBit_two_mul_add_one, show 2 * t / 2 = t by omega]
    generalize pdBit t = c
    revert c
    decide
  · subst ht
    rw [pdBit_two_mul_add_one, show 2 * t + 1 + 1 = 2 * (t + 1) by ring,
      pdBit_two_mul, show (2 * t + 1) / 2 = t by omega]
    generalize pdBit t = c
    revert c
    decide

/-! ### The two Hankel families -/

/-- The Hankel matrix of the period-doubling sequence. -/
def pdHankel (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  of fun i j => pdBit ((i : ℕ) + j)

/-- The Hankel matrix of the half-index period-doubling sequence. -/
def pdHankelHalf (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  of fun i j => pdBit (((i : ℕ) + j) / 2)

/-- `x·x = x` in `𝔽₂`. -/
theorem zmod_two_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

/-- Subtraction is addition in `𝔽₂`. -/
theorem zmod_two_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  revert a b
  decide

/-- `D(2n) = D(n)`. -/
theorem pdHankel_det_two_mul (n : ℕ) :
    (pdHankel (2 * n)).det = (pdHankel n).det := by
  rw [← det_submatrix_equiv_self (interleaveEquiv n) (pdHankel (2 * n))]
  have hform : (pdHankel (2 * n)).submatrix (interleaveEquiv n)
      (interleaveEquiv n) =
      fromBlocks (of fun _ _ : Fin n => (1 : ZMod 2))
        (of fun i j : Fin n => 1 + pdBit ((i : ℕ) + j))
        (of fun i j : Fin n => 1 + pdBit ((i : ℕ) + j))
        (of fun _ _ : Fin n => (1 : ZMod 2)) := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j) <;>
      simp only [submatrix_apply, pdHankel, of_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        interleaveEquiv_inl, interleaveEquiv_inr]
    · rw [show 2 * (i : ℕ) + 2 * (j : ℕ) = 2 * ((i : ℕ) + j) by ring]
      exact pdBit_two_mul _
    · rw [show 2 * (i : ℕ) + (2 * (j : ℕ) + 1) =
        2 * ((i : ℕ) + j) + 1 by ring]
      exact pdBit_two_mul_add_one _
    · rw [show 2 * (i : ℕ) + 1 + 2 * (j : ℕ) =
        2 * ((i : ℕ) + j) + 1 by ring]
      exact pdBit_two_mul_add_one _
    · rw [show 2 * (i : ℕ) + 1 + (2 * (j : ℕ) + 1) =
        2 * ((i : ℕ) + j + 1) by ring]
      exact pdBit_two_mul _
  have hPQ : (of fun _ _ : Fin n => (1 : ZMod 2)) +
      (of fun i j : Fin n => 1 + pdBit ((i : ℕ) + j)) = pdHankel n := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.add_apply, of_apply, pdHankel]
    generalize pdBit ((i : ℕ) + j) = c
    revert c
    decide
  have hPmQ : (of fun _ _ : Fin n => (1 : ZMod 2)) -
      (of fun i j : Fin n => 1 + pdBit ((i : ℕ) + j)) = pdHankel n := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.sub_apply, of_apply, pdHankel]
    generalize pdBit ((i : ℕ) + j) = c
    revert c
    decide
  rw [hform, det_fromBlocks_symm, hPQ, hPmQ, zmod_two_mul_self]

/-- `Y(2n) = D(n)·Y(n)`. -/
theorem pdHankelHalf_det_two_mul (n : ℕ) :
    (pdHankelHalf (2 * n)).det =
      (pdHankel n).det * (pdHankelHalf n).det := by
  rw [← det_submatrix_equiv_self (interleaveEquiv n)
    (pdHankelHalf (2 * n))]
  have hform : (pdHankelHalf (2 * n)).submatrix (interleaveEquiv n)
      (interleaveEquiv n) =
      fromBlocks (pdHankel n) (pdHankel n) (pdHankel n)
        (of fun i j : Fin n => pdBit ((i : ℕ) + j + 1)) := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j) <;>
      simp only [submatrix_apply, pdHankelHalf, of_apply, pdHankel,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, interleaveEquiv_inl, interleaveEquiv_inr] <;>
      congr 1 <;> omega
  have hmat : (of fun i j : Fin n => pdBit ((i : ℕ) + j + 1)) -
      1 * pdHankel n = pdHankelHalf n := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.one_mul, Matrix.sub_apply]
    simp only [of_apply, pdHankel, pdHankelHalf]
    rw [zmod_two_sub_eq_add, add_comm]
    exact pdBit_add_succ ((i : ℕ) + j)
  rw [hform, det_fromBlocks_of_eq_mul _ _ _ _ 1 (Matrix.one_mul _).symm,
    hmat]

/-- `Y(2n+1) = D(n+1)·Y(n)`. -/
theorem pdHankelHalf_det_two_mul_add_one (n : ℕ) :
    (pdHankelHalf (2 * n + 1)).det =
      (pdHankel (n + 1)).det * (pdHankelHalf n).det := by
  rw [← det_submatrix_equiv_self (interleaveOddEquiv n)
    (pdHankelHalf (2 * n + 1))]
  have hform : (pdHankelHalf (2 * n + 1)).submatrix (interleaveOddEquiv n)
      (interleaveOddEquiv n) =
      fromBlocks (pdHankel (n + 1))
        (of fun (i : Fin (n + 1)) (j : Fin n) => pdBit ((i : ℕ) + j))
        (of fun (i : Fin n) (j : Fin (n + 1)) => pdBit ((i : ℕ) + j))
        (of fun i j : Fin n => pdBit ((i : ℕ) + j + 1)) := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j) <;>
      simp only [submatrix_apply, pdHankelHalf, of_apply, pdHankel,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, interleaveOddEquiv_inl,
        interleaveOddEquiv_inr] <;>
      congr 1 <;> omega
  have hC : (of fun (i : Fin n) (j : Fin (n + 1)) =>
      pdBit ((i : ℕ) + j)) =
      (of fun (i : Fin n) (k : Fin (n + 1)) =>
        if k = Fin.castSucc i then (1 : ZMod 2) else 0) *
        pdHankel (n + 1) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [of_apply, pdHankel]
    rw [Finset.sum_eq_single (Fin.castSucc i)]
    · rw [if_pos rfl, one_mul, Fin.val_castSucc]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hmat : (of fun i j : Fin n => pdBit ((i : ℕ) + j + 1)) -
      (of fun (i : Fin n) (k : Fin (n + 1)) =>
        if k = Fin.castSucc i then (1 : ZMod 2) else 0) *
        (of fun (i : Fin (n + 1)) (j : Fin n) =>
          pdBit ((i : ℕ) + j)) = pdHankelHalf n := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.sub_apply, Matrix.mul_apply]
    simp only [of_apply, pdHankelHalf]
    rw [Finset.sum_eq_single (Fin.castSucc i)]
    · rw [if_pos rfl, one_mul, Fin.val_castSucc,
        zmod_two_sub_eq_add, add_comm]
      exact pdBit_add_succ ((i : ℕ) + j)
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hform, det_fromBlocks_of_eq_mul _ _ _ _ _ hC, hmat]

/-! ### The odd halving of `D`: the triple-triangular certificate -/

/-- `(1+c) + (1+d) = c + d` in `𝔽₂`. -/
theorem zmod_two_one_add_add (c d : ZMod 2) : 1 + c + (1 + d) = c + d := by
  revert c d
  decide

section DOdd

variable (n : ℕ)

/-- The superdiagonal shift matrix. -/
private def shiftU : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  of fun i k => if (k : ℕ) = (i : ℕ) + 1 then 1 else 0

private theorem shiftU_mul {α : Type*} (W : Matrix (Fin (n + 1)) α (ZMod 2))
    (i : Fin (n + 1)) (j : α) :
    (shiftU n * W) i j =
      if h : (i : ℕ) + 1 < n + 1 then W ⟨(i : ℕ) + 1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) + 1 < n + 1
  · rw [dif_pos h, Finset.sum_eq_single (⟨(i : ℕ) + 1, h⟩ : Fin (n + 1))]
    · rw [shiftU, of_apply, if_pos rfl, one_mul]
    · intro b _ hb
      rw [shiftU, of_apply,
        if_neg (fun hc => hb (Fin.ext hc)), zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [shiftU, of_apply, if_neg (by omega), zero_mul]

private theorem mul_shiftUT {α : Type*} [Fintype α]
    (W : Matrix α (Fin (n + 1)) (ZMod 2)) (i : α) (j : Fin (n + 1)) :
    (W * (shiftU n).transpose) i j =
      if h : (j : ℕ) + 1 < n + 1 then W i ⟨(j : ℕ) + 1, h⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : (j : ℕ) + 1 < n + 1
  · rw [dif_pos h, Finset.sum_eq_single (⟨(j : ℕ) + 1, h⟩ : Fin (n + 1))]
    · rw [Matrix.transpose_apply, shiftU, of_apply, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Matrix.transpose_apply, shiftU, of_apply,
        if_neg (fun hc => hb (Fin.ext hc)), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.transpose_apply, shiftU, of_apply, if_neg (by omega),
      mul_zero]

/-- The row-difference certificate. -/
private def deltaMat : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  1 + shiftU n

private theorem deltaMat_det : (deltaMat n).det = 1 := by
  have htri : (deltaMat n).BlockTriangular id := by
    intro i j hij
    have hij' : (j : ℕ) < (i : ℕ) := hij
    rw [deltaMat, Matrix.add_apply,
      Matrix.one_apply_ne (fun hc => by subst hc; exact lt_irrefl _ hij'),
      shiftU, of_apply, if_neg (by omega), add_zero]
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [deltaMat, Matrix.add_apply, Matrix.one_apply_eq, shiftU, of_apply,
    if_neg (by omega), add_zero]

private def deltaMatT : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  1 + (shiftU n).transpose

private theorem deltaMatT_det : (deltaMatT n).det = 1 := by
  have htri : (deltaMatT n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    rw [deltaMatT, Matrix.add_apply,
      Matrix.one_apply_ne (fun hc => by subst hc; exact lt_irrefl _ hij'),
      Matrix.transpose_apply, shiftU, of_apply, if_neg (by omega),
      add_zero]
  rw [Matrix.det_of_lowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [deltaMatT, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.transpose_apply, shiftU, of_apply, if_neg (by omega), add_zero]

/-- The top-left block after both eliminations. -/
private theorem topLeft_eq :
    deltaMat n * (of fun _ _ : Fin (n + 1) => (1 : ZMod 2)) *
      deltaMatT n =
      of fun i j : Fin (n + 1) =>
        if (i : ℕ) = n ∧ (j : ℕ) = n then 1 else 0 := by
  have hA : deltaMat n * (of fun _ _ : Fin (n + 1) => (1 : ZMod 2)) =
      of fun i _ : Fin (n + 1) =>
        if (i : ℕ) = n then (1 : ZMod 2) else 0 := by
    refine Matrix.ext fun i j => ?_
    rw [deltaMat, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
      shiftU_mul]
    by_cases h : (i : ℕ) + 1 < n + 1
    · rw [dif_pos h]
      simp only [of_apply]
      rw [if_neg (by omega)]
      decide
    · rw [dif_neg h]
      simp only [of_apply]
      rw [if_pos (by omega)]
      decide
  rw [hA]
  refine Matrix.ext fun i j => ?_
  rw [deltaMatT, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
    mul_shiftUT]
  by_cases h : (j : ℕ) + 1 < n + 1
  · have hnand : ¬((i : ℕ) = n ∧ (j : ℕ) = n) := by
      rintro ⟨h1, h2⟩
      omega
    rw [dif_pos h]
    simp only [of_apply]
    rw [if_neg hnand]
    by_cases hi : (i : ℕ) = n
    · rw [if_pos hi]
      decide
    · rw [if_neg hi]
      decide
  · rw [dif_neg h]
    simp only [of_apply]
    by_cases hi : (i : ℕ) = n
    · rw [if_pos hi,
        if_pos (⟨hi, by omega⟩ : (i : ℕ) = n ∧ (j : ℕ) = n)]
      decide
    · rw [if_neg hi,
        if_neg (fun hc : (i : ℕ) = n ∧ (j : ℕ) = n => hi hc.1)]
      decide

/-- The top-right block after the row elimination. -/
private theorem topRight_eq :
    deltaMat n * (of fun (i : Fin (n + 1)) (j : Fin n) =>
      1 + pdBit ((i : ℕ) + j)) =
      of fun (i : Fin (n + 1)) (j : Fin n) =>
        if (i : ℕ) < n then pdBit (((i : ℕ) + j) / 2)
        else 1 + pdBit ((i : ℕ) + j) := by
  refine Matrix.ext fun i j => ?_
  rw [deltaMat, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    shiftU_mul]
  by_cases h : (i : ℕ) + 1 < n + 1
  · rw [dif_pos h]
    simp only [of_apply]
    rw [if_pos (by omega : (i : ℕ) < n),
      show ((⟨(i : ℕ) + 1, h⟩ : Fin (n + 1)) : ℕ) + (j : ℕ) =
        (i : ℕ) + j + 1 from by dsimp only; omega,
      zmod_two_one_add_add, pdBit_add_succ]
  · rw [dif_neg h]
    simp only [of_apply]
    rw [if_neg (by omega : ¬(i : ℕ) < n), add_zero]

/-- The bottom-left block after the column elimination. -/
private theorem botLeft_eq :
    (of fun (i : Fin n) (j : Fin (n + 1)) => 1 + pdBit ((i : ℕ) + j)) *
      deltaMatT n =
      of fun (i : Fin n) (j : Fin (n + 1)) =>
        if (j : ℕ) < n then pdBit (((i : ℕ) + j) / 2)
        else 1 + pdBit ((i : ℕ) + j) := by
  refine Matrix.ext fun i j => ?_
  rw [deltaMatT, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
    mul_shiftUT]
  by_cases h : (j : ℕ) + 1 < n + 1
  · rw [dif_pos h]
    simp only [of_apply]
    rw [if_pos (by omega : (j : ℕ) < n),
      show (i : ℕ) + ((⟨(j : ℕ) + 1, h⟩ : Fin (n + 1)) : ℕ) =
        (i : ℕ) + j + 1 from by dsimp only; omega,
      zmod_two_one_add_add, pdBit_add_succ]
  · rw [dif_neg h]
    simp only [of_apply]
    rw [if_neg (by omega : ¬(j : ℕ) < n), add_zero]

/-- The column-reordering permutation for the odd `D`-halving. -/
private def colShuffle : Equiv.Perm (Fin (n + 1) ⊕ Fin n) where
  toFun := Sum.elim
    (fun k => if h : (k : ℕ) < n then Sum.inr ⟨k, h⟩
      else Sum.inl (Fin.last n))
    fun j => Sum.inl (Fin.castSucc j)
  invFun := Sum.elim
    (fun j => if h : (j : ℕ) < n then Sum.inr ⟨j, h⟩
      else Sum.inl (Fin.last n))
    fun k => Sum.inl (Fin.castSucc k)
  left_inv := by
    rintro (k | j)
    · dsimp only [Sum.elim_inl]
      by_cases h : (k : ℕ) < n
      · rw [dif_pos h]
        dsimp only [Sum.elim_inr]
        exact congrArg Sum.inl (Fin.ext (by rw [Fin.val_castSucc]))
      · rw [dif_neg h]
        dsimp only [Sum.elim_inl]
        rw [dif_neg (show ¬((Fin.last n : Fin (n + 1)) : ℕ) < n by
          rw [Fin.val_last]; omega)]
        exact congrArg Sum.inl (Fin.ext (by rw [Fin.val_last]; omega))
    · dsimp only [Sum.elim_inr, Sum.elim_inl]
      rw [dif_pos (show ((Fin.castSucc j : Fin (n + 1)) : ℕ) < n by
        rw [Fin.val_castSucc]; omega)]
      exact congrArg Sum.inr (Fin.ext (by rw [Fin.val_castSucc]))
  right_inv := by
    rintro (j | k)
    · dsimp only [Sum.elim_inl]
      by_cases h : (j : ℕ) < n
      · rw [dif_pos h]
        dsimp only [Sum.elim_inr]
        exact congrArg Sum.inl (Fin.ext (by rw [Fin.val_castSucc]))
      · rw [dif_neg h]
        dsimp only [Sum.elim_inl]
        rw [dif_neg (show ¬((Fin.last n : Fin (n + 1)) : ℕ) < n by
          rw [Fin.val_last]; omega)]
        exact congrArg Sum.inl (Fin.ext (by rw [Fin.val_last]; omega))
    · dsimp only [Sum.elim_inr, Sum.elim_inl]
      rw [dif_pos (show ((Fin.castSucc k : Fin (n + 1)) : ℕ) < n by
        rw [Fin.val_castSucc]; omega)]
      exact congrArg Sum.inr (Fin.ext (by rw [Fin.val_castSucc]))

private theorem colShuffle_inl_lt (j : Fin (n + 1)) (h : (j : ℕ) < n) :
    (colShuffle n) (Sum.inl j) =
      (Sum.inr ⟨(j : ℕ), h⟩ : Fin (n + 1) ⊕ Fin n) := by
  simp only [colShuffle, Equiv.coe_fn_mk, Sum.elim_inl]
  rw [dif_pos h]

private theorem colShuffle_inl_ge (j : Fin (n + 1)) (h : ¬(j : ℕ) < n) :
    (colShuffle n) (Sum.inl j) =
      (Sum.inl (Fin.last n) : Fin (n + 1) ⊕ Fin n) := by
  simp only [colShuffle, Equiv.coe_fn_mk, Sum.elim_inl]
  rw [dif_neg h]

private theorem colShuffle_inr (j : Fin n) :
    (colShuffle n) (Sum.inr j) =
      (Sum.inl (Fin.castSucc j) : Fin (n + 1) ⊕ Fin n) := by
  simp only [colShuffle, Equiv.coe_fn_mk, Sum.elim_inr]

end DOdd

/-- Permutation signs are invisible in `𝔽₂`. -/
theorem sign_cast_zmod_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    ((Equiv.Perm.sign σ : ℤˣ) : ZMod 2) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;>
    decide

/-- `D(2n+1) = Y(n)`. -/
theorem pdHankel_det_two_mul_add_one (n : ℕ) :
    (pdHankel (2 * n + 1)).det = (pdHankelHalf n).det := by
  classical
  rw [← det_submatrix_equiv_self (interleaveOddEquiv n)
    (pdHankel (2 * n + 1))]
  have hform : (pdHankel (2 * n + 1)).submatrix (interleaveOddEquiv n)
      (interleaveOddEquiv n) =
      fromBlocks (of fun _ _ : Fin (n + 1) => (1 : ZMod 2))
        (of fun (i : Fin (n + 1)) (j : Fin n) =>
          1 + pdBit ((i : ℕ) + j))
        (of fun (i : Fin n) (j : Fin (n + 1)) =>
          1 + pdBit ((i : ℕ) + j))
        (of fun _ _ : Fin n => (1 : ZMod 2)) := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j) <;>
      simp only [submatrix_apply, pdHankel, of_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        interleaveOddEquiv_inl, interleaveOddEquiv_inr]
    · rw [show 2 * (i : ℕ) + 2 * (j : ℕ) = 2 * ((i : ℕ) + j) by ring]
      exact pdBit_two_mul _
    · rw [show 2 * (i : ℕ) + (2 * (j : ℕ) + 1) =
        2 * ((i : ℕ) + j) + 1 by ring]
      exact pdBit_two_mul_add_one _
    · rw [show 2 * (i : ℕ) + 1 + 2 * (j : ℕ) =
        2 * ((i : ℕ) + j) + 1 by ring]
      exact pdBit_two_mul_add_one _
    · rw [show 2 * (i : ℕ) + 1 + (2 * (j : ℕ) + 1) =
        2 * ((i : ℕ) + j + 1) by ring]
      exact pdBit_two_mul _
  rw [hform]
  have hL : (fromBlocks (deltaMat n)
      (0 : Matrix (Fin (n + 1)) (Fin n) (ZMod 2))
      (0 : Matrix (Fin n) (Fin (n + 1)) (ZMod 2))
      (1 : Matrix (Fin n) (Fin n) (ZMod 2))).det = 1 := by
    rw [det_fromBlocks_zero₂₁, deltaMat_det, det_one, mul_one]
  have hR : (fromBlocks (deltaMatT n)
      (0 : Matrix (Fin (n + 1)) (Fin n) (ZMod 2))
      (0 : Matrix (Fin n) (Fin (n + 1)) (ZMod 2))
      (1 : Matrix (Fin n) (Fin n) (ZMod 2))).det = 1 := by
    rw [det_fromBlocks_zero₂₁, deltaMatT_det, det_one, mul_one]
  have hdetM : (fromBlocks (of fun _ _ : Fin (n + 1) => (1 : ZMod 2))
      (of fun (i : Fin (n + 1)) (j : Fin n) => 1 + pdBit ((i : ℕ) + j))
      (of fun (i : Fin n) (j : Fin (n + 1)) => 1 + pdBit ((i : ℕ) + j))
      (of fun _ _ : Fin n => (1 : ZMod 2))).det =
      ((fromBlocks (deltaMat n) 0 0 1) *
        fromBlocks (of fun _ _ : Fin (n + 1) => (1 : ZMod 2))
          (of fun (i : Fin (n + 1)) (j : Fin n) =>
            1 + pdBit ((i : ℕ) + j))
          (of fun (i : Fin n) (j : Fin (n + 1)) =>
            1 + pdBit ((i : ℕ) + j))
          (of fun _ _ : Fin n => (1 : ZMod 2)) *
        (fromBlocks (deltaMatT n) 0 0 1)).det := by
    rw [det_mul, det_mul, hL, hR, one_mul, mul_one]
  rw [hdetM, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add]
  rw [topLeft_eq, topRight_eq, botLeft_eq]
  have hperm := Matrix.det_permute' (colShuffle n)
    (fromBlocks
      (of fun i k : Fin (n + 1) =>
        if (i : ℕ) = n ∧ (k : ℕ) = n then 1 else 0)
      (of fun (i : Fin (n + 1)) (j : Fin n) =>
        if (i : ℕ) < n then pdBit (((i : ℕ) + j) / 2)
        else 1 + pdBit ((i : ℕ) + j))
      (of fun (i : Fin n) (k : Fin (n + 1)) =>
        if (k : ℕ) < n then pdBit (((i : ℕ) + k) / 2)
        else 1 + pdBit ((i : ℕ) + k))
      (of fun _ _ : Fin n => (1 : ZMod 2)))
  rw [sign_cast_zmod_two, one_mul] at hperm
  rw [← hperm]
  have hfinal : (fromBlocks
      (of fun i k : Fin (n + 1) =>
        if (i : ℕ) = n ∧ (k : ℕ) = n then 1 else 0)
      (of fun (i : Fin (n + 1)) (j : Fin n) =>
        if (i : ℕ) < n then pdBit (((i : ℕ) + j) / 2)
        else 1 + pdBit ((i : ℕ) + j))
      (of fun (i : Fin n) (k : Fin (n + 1)) =>
        if (k : ℕ) < n then pdBit (((i : ℕ) + k) / 2)
        else 1 + pdBit ((i : ℕ) + k))
      (of fun _ _ : Fin n => (1 : ZMod 2))).submatrix id
        (colShuffle n) = fromBlocks
      (of fun i k : Fin (n + 1) =>
        if (k : ℕ) < n then
          (if (i : ℕ) < n then pdBit (((i : ℕ) + k) / 2)
            else 1 + pdBit ((i : ℕ) + k))
        else (if (i : ℕ) = n then 1 else 0))
      (0 : Matrix (Fin (n + 1)) (Fin n) (ZMod 2))
      (of fun (i : Fin n) (k : Fin (n + 1)) =>
        if (k : ℕ) < n then 1 else 1 + pdBit ((i : ℕ) + n))
      (pdHankelHalf n) := by
    refine Matrix.ext ?_
    rintro (i | i) (j | j) <;>
      simp only [submatrix_apply, id_eq]
    · rcases Nat.lt_or_ge (j : ℕ) n with hj | hj
      · rw [colShuffle_inl_lt n j hj]
        simp only [fromBlocks_apply₁₂, fromBlocks_apply₁₁, of_apply]
        rw [if_pos hj]
      · rw [colShuffle_inl_ge n j (by omega)]
        simp only [fromBlocks_apply₁₁, of_apply]
        rw [if_neg (show ¬(j : ℕ) < n by omega)]
        by_cases hi : (i : ℕ) = n
        · rw [if_pos hi, if_pos ⟨hi, Fin.val_last n⟩]
        · rw [if_neg hi, if_neg (fun hc => hi hc.1)]
    · rw [colShuffle_inr n j]
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, of_apply,
        Matrix.zero_apply]
      rw [if_neg (fun hc => by
        have h2 := hc.2
        rw [Fin.val_castSucc] at h2
        omega)]
    · rcases Nat.lt_or_ge (j : ℕ) n with hj | hj
      · rw [colShuffle_inl_lt n j hj]
        simp only [fromBlocks_apply₂₂, fromBlocks_apply₂₁, of_apply]
        rw [if_pos hj]
      · rw [colShuffle_inl_ge n j (by omega)]
        simp only [fromBlocks_apply₂₁, of_apply]
        rw [if_neg (show ¬(j : ℕ) < n by omega),
          if_neg (show ¬((Fin.last n : Fin (n + 1)) : ℕ) < n by
            rw [Fin.val_last]; omega), Fin.val_last]
    · rw [colShuffle_inr n j]
      simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply,
        pdHankelHalf]
      rw [if_pos (show ((Fin.castSucc j : Fin (n + 1)) : ℕ) < n by
        rw [Fin.val_castSucc]; omega), Fin.val_castSucc]
  rw [hfinal, det_fromBlocks_zero₁₂]
  have hlead : (of fun i k : Fin (n + 1) =>
      if (k : ℕ) < n then
        (if (i : ℕ) < n then pdBit (((i : ℕ) + k) / 2)
          else 1 + pdBit ((i : ℕ) + k))
      else (if (i : ℕ) = n then 1 else 0)).det =
      (pdHankelHalf n).det := by
    rw [← det_submatrix_equiv_self
      (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))]
    have hvl : ∀ i : Fin n,
        ((finSumFinEquiv (Sum.inl i) : Fin (n + 1)) : ℕ) = (i : ℕ) := by
      intro i
      simp
    have hvr : ∀ i : Fin 1,
        ((finSumFinEquiv (Sum.inr i) : Fin (n + 1)) : ℕ) = n := by
      intro i
      have h0 : (i : ℕ) = 0 := by omega
      simp
    have hsub : (of fun i k : Fin (n + 1) =>
        if (k : ℕ) < n then
          (if (i : ℕ) < n then pdBit (((i : ℕ) + k) / 2)
            else 1 + pdBit ((i : ℕ) + k))
        else (if (i : ℕ) = n then 1 else 0)).submatrix finSumFinEquiv
          finSumFinEquiv = fromBlocks (pdHankelHalf n)
        (0 : Matrix (Fin n) (Fin 1) (ZMod 2))
        (of fun (_ : Fin 1) (k : Fin n) => 1 + pdBit (n + k))
        (of fun _ _ : Fin 1 => (1 : ZMod 2)) := by
      refine Matrix.ext ?_
      rintro (i | i) (j | j) <;>
        simp only [submatrix_apply, of_apply, fromBlocks_apply₁₁,
          fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
          Matrix.zero_apply, pdHankelHalf]
      · rw [hvl i, hvl j, if_pos j.isLt, if_pos i.isLt]
      · rw [hvl i, hvr j, if_neg (by omega), if_neg (by omega)]
      · rw [hvr i, hvl j, if_pos j.isLt, if_neg (by omega)]
      · rw [hvr i, hvr j, if_neg (by omega), if_pos rfl]
    rw [hsub, det_fromBlocks_zero₁₂]
    have h1 : (of fun _ _ : Fin 1 => (1 : ZMod 2)).det = 1 := by
      rw [det_fin_one, of_apply]
    rw [h1, mul_one]
  rw [hlead, zmod_two_mul_self]

/-! ### The strong induction: every determinant is one -/

/-- **All Hankel determinants of the period-doubling sequence over
`𝔽₂` equal `1`** — and so do those of its half-index companion. -/
theorem pdHankel_det_eq_one :
    ∀ n : ℕ, (pdHankel n).det = 1 ∧ (pdHankelHalf n).det = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨Matrix.det_isEmpty, Matrix.det_isEmpty⟩
    | 1 =>
        have h0 : pdBit 0 = 1 := by
          have h := pdBit_two_mul 0
          simpa using h
        constructor
        · rw [det_fin_one]
          show pdBit ((0 : ℕ) + 0) = 1
          simpa using h0
        · rw [det_fin_one]
          show pdBit (((0 : ℕ) + 0) / 2) = 1
          simpa using h0
    | (m + 2) =>
        rcases Nat.even_or_odd (m + 2) with ⟨t, ht⟩ | ⟨t, ht⟩
        · have ht' : m + 2 = 2 * t := by omega
          have htlt : t < m + 2 := by omega
          constructor
          · rw [ht', pdHankel_det_two_mul, (ih t htlt).1]
          · rw [ht', pdHankelHalf_det_two_mul, (ih t htlt).1,
              (ih t htlt).2, one_mul]
        · have ht' : m + 2 = 2 * t + 1 := by omega
          have htlt : t < m + 2 := by omega
          have ht1lt : t + 1 < m + 2 := by omega
          constructor
          · rw [ht', pdHankel_det_two_mul_add_one, (ih t htlt).2]
          · rw [ht', pdHankelHalf_det_two_mul_add_one,
              (ih (t + 1) ht1lt).1, (ih t htlt).2, one_mul]

end Fabius
