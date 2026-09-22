import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Surreal.Algebra.Complexify

/-!
# The negative-atom Toeplitz example

This file proves the finite algebraic clauses of `thm:negativeatom`,
`thm:quadrature` and `thm:schur` in
`docs/surcomplex/hahn-herglotz-positivity/article.tex`.

The moments `c_0 = 1`, `c_n = -ε` for `n ≠ 0` have Toeplitz matrices
`T_N(c) = (1 + ε) I - ε J`. The all-ones vector has eigenvalue `1 - Nε`, every
vector with coordinate sum zero has eigenvalue `1 + ε`, and
`det T_N(c) = (1 + ε)^N (1 - Nε)`. Over an ordered field, `0 ≤ ε` and `Nε < 1`
make both the real quadratic form and the Hermitian form over the
complexification strictly positive on nonzero vectors. For a positive
infinitesimal `ε` in a Hahn field these hypotheses hold for every ordinary
finite `N`, which is the non-Archimedean phenomenon of `thm:negativeatom`.

The positive quadrature of `thm:quadrature` uses weights `(1 + ε)/M` at the
`M`th roots of unity, reduced by `ε` at `1`. Its weights are positive when
`(M - 1)ε < 1`, and its moments are `1` at zero and `-ε` for `0 < |n| < M`.

The normalized Cayley quotient of `H_ε(z) = 1 - 2εz/(1 - z)` and all its exact
Schur iterates are the rational functions of `eq:schurformula`, with parameters
`α_n = -ε/(1 - nε)` and poles at `r_n = (1 - nε)/(1 - (n - 1)ε)`. The
measure-theoretic uniqueness of the representing signed measure is a separate
obligation.
-/

namespace Surreal.Herglotz

open Matrix Finset

noncomputable section

section Toeplitz

variable {F : Type*} [Field F]

/-- `T_N(c) = (c_{j-k})_{0 ≤ j,k ≤ N}` for a moment sequence indexed by integers. -/
def toeplitz (N : ℕ) (c : ℤ → F) : Matrix (Fin (N + 1)) (Fin (N + 1)) F :=
  Matrix.of fun j k => c ((j : ℤ) - k)

/-- `eq:mainmoments`: `c_0 = 1` and `c_n = -ε` for `n ≠ 0`. -/
def negAtomMoment (ε : F) (n : ℤ) : F :=
  if n = 0 then 1 else -ε

/-- The all-ones matrix `J`. -/
def allOnes (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) F :=
  Matrix.of fun _ _ => 1

/-- `eq:mainmatrix`: `T_N(c) = (1 + ε) I - ε J`. -/
theorem toeplitz_negAtomMoment (N : ℕ) (ε : F) :
    toeplitz N (negAtomMoment ε) = (1 + ε) • (1 : Matrix _ _ F) - ε • allOnes N := by
  ext j k
  by_cases hjk : j = k
  · subst hjk
    simp [toeplitz, negAtomMoment, allOnes]
  · have : (j : ℤ) - k ≠ 0 := by
      intro h
      exact hjk (Fin.ext (by omega))
    simp [toeplitz, negAtomMoment, allOnes, this, one_apply_ne hjk]

theorem allOnes_mulVec (N : ℕ) (v : Fin (N + 1) → F) :
    allOnes N *ᵥ v = fun _ => ∑ j, v j := by
  funext j
  simp [allOnes, mulVec, dotProduct]

theorem toeplitz_negAtomMoment_mulVec (N : ℕ) (ε : F) (v : Fin (N + 1) → F) :
    toeplitz N (negAtomMoment ε) *ᵥ v = (1 + ε) • v - ε • fun _ => ∑ j, v j := by
  rw [toeplitz_negAtomMoment, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
    allOnes_mulVec]

/-- `eq:eigen`: the constant vector has eigenvalue `1 - Nε`. -/
theorem toeplitz_negAtomMoment_mulVec_one (N : ℕ) (ε : F) :
    toeplitz N (negAtomMoment ε) *ᵥ (fun _ => 1) = (1 - N * ε) • (fun _ => (1 : F)) := by
  rw [toeplitz_negAtomMoment_mulVec]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- `eq:eigen`: every vector with coordinate sum zero has eigenvalue `1 + ε`;
these vectors form a subspace of dimension `N`. -/
theorem toeplitz_negAtomMoment_mulVec_of_sum_eq_zero (N : ℕ) (ε : F)
    {v : Fin (N + 1) → F} (hv : ∑ j, v j = 0) :
    toeplitz N (negAtomMoment ε) *ᵥ v = (1 + ε) • v := by
  rw [toeplitz_negAtomMoment_mulVec, hv]
  funext j
  simp

/-- `eq:det`: the determinant of the negative-atom Toeplitz matrix. -/
theorem det_toeplitz_negAtomMoment (N : ℕ) {ε : F} (hε : 1 + ε ≠ 0) :
    (toeplitz N (negAtomMoment ε)).det = (1 + ε) ^ N * (1 - N * ε) := by
  have hc : (1 + ε) * (-ε / (1 + ε)) = -ε := mul_div_cancel₀ _ hε
  have hrank : (1 + ε) • (replicateCol (Fin 1) (fun _ : Fin (N + 1) => (1 : F)) *
      replicateRow (Fin 1) (fun _ : Fin (N + 1) => -ε / (1 + ε))) = -(ε • allOnes N) := by
    ext j k
    simp [mul_apply, allOnes, hc]
  have hdecomp : toeplitz N (negAtomMoment ε) = (1 + ε) •
      (1 + replicateCol (Fin 1) (fun _ : Fin (N + 1) => (1 : F)) *
        replicateRow (Fin 1) (fun _ : Fin (N + 1) => -ε / (1 + ε))) := by
    rw [toeplitz_negAtomMoment, smul_add, hrank, sub_eq_add_neg]
  rw [hdecomp, det_smul, det_one_add_mul_comm, det_unique]
  simp only [Matrix.add_apply, one_apply_eq, mul_apply, replicateRow_apply, replicateCol_apply,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  rw [pow_succ, mul_assoc]
  congr 1
  rw [mul_add, mul_one, mul_left_comm, hc]
  ring

end Toeplitz

section Hermitian

variable {F : Type*} [Field F]

open Complexify

/-- The Hermitian form `x* A x` of a base-field matrix over the complexification. -/
def hermForm {m : Type*} [Fintype m] (A : Matrix m m F) (x : m → Complexify F) :
    Complexify F :=
  ∑ j, ∑ k, star (x j) * algebraMap F (Complexify F) (A j k) * x k

theorem star_mul_self_eq (z : Complexify F) :
    star z * z = algebraMap F (Complexify F) (normSq z) := by
  rw [mul_comm, mul_conj]

theorem hermForm_smul_sub_smul {m : Type*} [Fintype m] (a b : F) (A B : Matrix m m F)
    (x : m → Complexify F) :
    hermForm (a • A - b • B) x = algebraMap F (Complexify F) a * hermForm A x -
      algebraMap F (Complexify F) b * hermForm B x := by
  simp only [hermForm, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem hermForm_one {m : Type*} [Fintype m] [DecidableEq m] (x : m → Complexify F) :
    hermForm (1 : Matrix m m F) x = algebraMap F (Complexify F) (∑ j, normSq (x j)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hkj => by simp [one_apply_ne (Ne.symm hkj)])
    (fun h => absurd (mem_univ j) h)]
  simp [star_mul_self_eq]

theorem hermForm_allOnes (N : ℕ) (x : Fin (N + 1) → Complexify F) :
    hermForm (allOnes N) x = algebraMap F (Complexify F) (normSq (∑ j, x j)) := by
  simp only [hermForm, allOnes, of_apply, map_one, mul_one]
  rw [← star_mul_self_eq, star_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

/-- The Hermitian form of `T_N(c)` over the complexification is real and equals
`(1 + ε)∑|x_j|² - ε|∑ x_j|²`. -/
theorem hermForm_toeplitz_negAtomMoment (N : ℕ) (ε : F) (x : Fin (N + 1) → Complexify F) :
    hermForm (toeplitz N (negAtomMoment ε)) x =
      algebraMap F (Complexify F)
        ((1 + ε) * ∑ j, normSq (x j) - ε * normSq (∑ j, x j)) := by
  rw [toeplitz_negAtomMoment, hermForm_smul_sub_smul, hermForm_one, hermForm_allOnes, map_sub,
    map_mul, map_mul]

end Hermitian

section Positivity

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open Complexify

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The real quadratic form of `T_N(c)` is `(1 + ε)|x|² - ε(∑ x)²`. -/
theorem dotProduct_toeplitz_negAtomMoment (N : ℕ) (ε : F) (x : Fin (N + 1) → F) :
    x ⬝ᵥ (toeplitz N (negAtomMoment ε) *ᵥ x) =
      (1 + ε) * ∑ j, x j ^ 2 - ε * (∑ j, x j) ^ 2 := by
  rw [toeplitz_negAtomMoment]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct, allOnes, mulVec, of_apply, one_mul, Finset.sum_mul,
    Finset.mul_sum, sq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The key inequality: `(1 - Nε)|x|² ≤ (1 + ε)|x|² - ε(∑ x)²` for `0 ≤ ε`. -/
theorem sub_mul_sum_sq_le (N : ℕ) {ε : F} (hε : 0 ≤ ε) (x : Fin (N + 1) → F) :
    (1 - N * ε) * ∑ j, x j ^ 2 ≤ (1 + ε) * ∑ j, x j ^ 2 - ε * (∑ j, x j) ^ 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (N + 1)))) (f := x)
  simp only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hcs
  nlinarith [mul_le_mul_of_nonneg_left hcs hε]

/-- `thm:negativeatom`: `T_N(c) ≻ 0` as a real quadratic form whenever `0 ≤ ε`
and `Nε < 1`, in particular for every ordinary `N` when `ε` is a positive
infinitesimal. -/
theorem toeplitz_negAtomMoment_posDef (N : ℕ) {ε : F} (hε : 0 ≤ ε) (hNε : N * ε < 1)
    {x : Fin (N + 1) → F} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (toeplitz N (negAtomMoment ε) *ᵥ x) := by
  rw [dotProduct_toeplitz_negAtomMoment]
  have hpos : 0 < ∑ j, x j ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj)))
      (single_le_sum (fun i _ => sq_nonneg (x i)) (mem_univ j))
  exact lt_of_lt_of_le (mul_pos (by linarith) hpos) (sub_mul_sum_sq_le N hε x)

/-- `eq:det`: the determinant is positive under the same hypotheses. -/
theorem det_toeplitz_negAtomMoment_pos (N : ℕ) {ε : F} (hε : 0 ≤ ε) (hNε : N * ε < 1) :
    0 < (toeplitz N (negAtomMoment ε)).det := by
  rw [det_toeplitz_negAtomMoment N (by linarith)]
  exact mul_pos (pow_pos (by linarith) N) (by linarith)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem re_sum {m : Type*} (s : Finset m) (x : m → Complexify F) :
    (∑ j ∈ s, x j).re = ∑ j ∈ s, (x j).re := by
  exact map_sum (QuadraticAlgebra.reₗ (R := F) (-1) 0) x s

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem im_sum {m : Type*} (s : Finset m) (x : m → Complexify F) :
    (∑ j ∈ s, x j).im = ∑ j ∈ s, (x j).im := by
  exact map_sum (QuadraticAlgebra.imₗ (R := F) (-1) 0) x s

/-- `thm:negativeatom`: `T_N(c) ≻ 0` against all complex Hahn vectors, whenever
`0 ≤ ε` and `Nε < 1`. -/
theorem hermForm_toeplitz_negAtomMoment_pos (N : ℕ) {ε : F} (hε : 0 ≤ ε) (hNε : N * ε < 1)
    {x : Fin (N + 1) → Complexify F} (hx : x ≠ 0) :
    0 < (1 + ε) * ∑ j, normSq (x j) - ε * normSq (∑ j, x j) := by
  have hpos : 0 < ∑ j, normSq (x j) := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (normSq_pos hj) (single_le_sum (fun i _ => normSq_nonneg (x i))
      (mem_univ j))
  have hre := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (N + 1))))
    (f := fun j => (x j).re)
  have him := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (N + 1))))
    (f := fun j => (x j).im)
  simp only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hre him
  have hnorm : normSq (∑ j, x j) ≤ ((N : F) + 1) * ∑ j, normSq (x j) := by
    simp only [normSq, re_sum, im_sum, Finset.sum_add_distrib]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hnorm hε]

end Positivity

section Schur

variable {F : Type*} [Field F]

/-- `eq:badH`: the rational Herglotz function of the negative-atom moments. -/
def negAtomHerglotz (ε z : F) : F :=
  1 - 2 * ε * z / (1 - z)

/-- `eq:schurformula`: the `n`th Schur iterate. -/
def schurIterate (ε z : F) (n : ℕ) : F :=
  -ε / (1 - n * ε - (1 - (n - 1) * ε) * z)

/-- `eq:schurformula`: the `n`th Schur parameter `α_n = s_n(0)`. -/
def schurParam (ε : F) (n : ℕ) : F :=
  -ε / (1 - n * ε)

theorem schurIterate_zero_arg (ε : F) (n : ℕ) : schurIterate ε 0 n = schurParam ε n := by
  simp [schurIterate, schurParam]

/-- `thm:schur`: the normalized Cayley quotient of `H_ε` is `s_0`. The factor `2`
must be invertible; ordered fields satisfy this. -/
theorem cayley_negAtomHerglotz {ε z : F} (two : (2 : F) ≠ 0) (hz : z ≠ 0) (h1 : 1 - z ≠ 0)
    (h2 : 1 - (1 + ε) * z ≠ 0) :
    (negAtomHerglotz ε z - 1) / (z * (negAtomHerglotz ε z + 1)) = schurIterate ε z 0 := by
  have h3 : negAtomHerglotz ε z + 1 = 2 * (1 - (1 + ε) * z) / (1 - z) := by
    rw [negAtomHerglotz, eq_div_iff h1, add_mul, sub_mul, div_mul_cancel₀ _ h1]
    ring
  have h4 : negAtomHerglotz ε z - 1 = -2 * ε * z / (1 - z) := by
    rw [negAtomHerglotz, eq_div_iff h1, sub_mul, sub_mul, div_mul_cancel₀ _ h1]
    ring
  have hR : (1 : F) - ((0 : ℕ) : F) * ε - (1 - (((0 : ℕ) : F) - 1) * ε) * z =
      1 - (1 + ε) * z := by
    push_cast
    ring
  rw [h3, h4, schurIterate, hR, mul_div_assoc', div_div_div_cancel_right₀ h1,
    div_eq_div_iff (mul_ne_zero hz (mul_ne_zero two h2)) h2]
  ring

/-- `eq:schurrec`: the Schur recursion is solved exactly by `eq:schurformula`.
The Schur parameter is real, so conjugation is omitted. -/
theorem schur_step {ε z : F} {n : ℕ} (hz : z ≠ 0) (h1 : 1 - n * ε ≠ 0)
    (h2 : 1 - (n - 1) * ε ≠ 0) (hD : 1 - n * ε - (1 - (n - 1) * ε) * z ≠ 0)
    (hD' : 1 - (n + 1) * ε - (1 - n * ε) * z ≠ 0) :
    (schurIterate ε z n - schurParam ε n) /
        (z * (1 - schurParam ε n * schurIterate ε z n)) = schurIterate ε z (n + 1) := by
  set D := 1 - n * ε - (1 - (n - 1) * ε) * z with hDdef
  set D' := 1 - (n + 1) * ε - (1 - n * ε) * z with hD'def
  have hnum : schurIterate ε z n - schurParam ε n =
      -ε * (1 - (n - 1) * ε) * z / (D * (1 - n * ε)) := by
    rw [schurIterate, schurParam, ← hDdef, div_sub_div _ _ hD h1,
      div_eq_div_iff (mul_ne_zero hD h1) (mul_ne_zero hD h1)]
    ring
  have hden : 1 - schurParam ε n * schurIterate ε z n =
      (1 - (n - 1) * ε) * D' / (D * (1 - n * ε)) := by
    rw [schurIterate, schurParam, ← hDdef, div_mul_div_comm, one_sub_div (mul_ne_zero h1 hD),
      div_eq_div_iff (mul_ne_zero h1 hD) (mul_ne_zero hD h1)]
    ring
  have hcast : (1 : F) - ((n + 1 : ℕ) : F) * ε - (1 - (((n + 1 : ℕ) : F) - 1) * ε) * z = D' := by
    push_cast
    ring
  rw [hnum, hden, schurIterate, hcast, mul_div_assoc',
    div_div_div_cancel_right₀ (mul_ne_zero hD h1),
    div_eq_div_iff (mul_ne_zero hz (mul_ne_zero h2 hD')) hD']
  ring

/-- `eq:schurpole`: `s_n` has a pole at `r_n = (1 - nε)/(1 - (n - 1)ε)`. -/
theorem schurIterate_denominator_eq_zero {ε : F} {n : ℕ} (h2 : 1 - (n - 1) * ε ≠ 0) :
    1 - n * ε - (1 - (n - 1) * ε) * ((1 - n * ε) / (1 - (n - 1) * ε)) = 0 := by
  rw [mul_div_cancel₀ _ h2, sub_self]

/-- The pole differs from `1` by `ε/(1 - (n - 1)ε)`, so its standard part is `1`
when `ε` is infinitesimal. -/
theorem one_sub_schurPole {ε : F} {n : ℕ} (h2 : 1 - (n - 1) * ε ≠ 0) :
    1 - (1 - n * ε) / (1 - (n - 1) * ε) = ε / (1 - (n - 1) * ε) := by
  rw [one_sub_div h2]
  congr 1
  ring

/-- `eq:boundarynegative`: `H_ε(1 - ε) = -1 + 2ε`. -/
theorem negAtomHerglotz_one_sub {ε : F} (hε : ε ≠ 0) :
    negAtomHerglotz ε (1 - ε) = -1 + 2 * ε := by
  rw [negAtomHerglotz, sub_sub_cancel, mul_comm 2 ε, mul_assoc, mul_div_cancel_left₀ _ hε]
  ring

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- `thm:schur`: each ordinary Schur parameter lies strictly inside the unit disk. -/
theorem abs_schurParam_lt_one {ε : F} {n : ℕ} (hε : 0 < ε) (hn : (n + 1) * ε < 1) :
    |schurParam ε n| < 1 := by
  have h1 : 0 < 1 - n * ε := by nlinarith
  rw [schurParam, abs_div, abs_neg, abs_of_pos hε, abs_of_pos h1, div_lt_one h1]
  nlinarith

/-- `eq:schurpole`: the pole lies in the open interval `(0, 1)`. -/
theorem schurPole_mem_Ioo {ε : F} {n : ℕ} (hε : 0 < ε) (hn : n * ε < 1) :
    (1 - n * ε) / (1 - (n - 1) * ε) ∈ Set.Ioo (0 : F) 1 := by
  have h1 : 0 < 1 - n * ε := by linarith
  have h2 : 0 < 1 - (n - 1) * ε := by nlinarith
  refine ⟨div_pos h1 h2, (div_lt_one h2).mpr (by nlinarith)⟩

end Schur

section Quadrature

variable {F : Type*} [Field F]

/-- `eq:quadrature`: weight `(1 + ε)/M` at every `M`th root of unity, reduced by
`ε` at the root `1`. -/
def quadratureWeight (M : ℕ) (ε : F) (k : ℕ) : F :=
  (1 + ε) / M - if k = 0 then ε else 0

/-- `thm:quadrature`: the quadrature is a Hahn probability. -/
theorem sum_quadratureWeight {M : ℕ} (hM : (M : F) ≠ 0) (ε : F) :
    ∑ k ∈ range M, quadratureWeight M ε k = 1 := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => hM (by simp [h])
  simp only [quadratureWeight, Finset.sum_sub_distrib, Finset.sum_const, card_range,
    nsmul_eq_mul, Finset.sum_ite_eq', mem_range, if_pos hM0]
  field_simp
  ring

/-- `thm:quadrature`: the moments of the quadrature at a primitive `M`th root of
unity are `1` at zero and `-ε` for `0 < n < M`. -/
theorem quadrature_moment {M : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ M) (hM : (M : F) ≠ 0)
    (ε : F) {n : ℕ} (hn : n < M) :
    ∑ k ∈ range M, quadratureWeight M ε k * (ζ ^ k) ^ n = if n = 0 then 1 else -ε := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => hM (by simp [h])
  have hsplit : ∑ k ∈ range M, quadratureWeight M ε k * (ζ ^ k) ^ n =
      (1 + ε) / M * ∑ k ∈ range M, (ζ ^ n) ^ k - ε := by
    simp only [quadratureWeight, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, ite_mul,
      zero_mul, Finset.sum_ite_eq', mem_range, if_pos hM0, pow_zero, one_pow, mul_one]
    rw [Finset.sum_congr rfl fun k _ => pow_right_comm ζ k n]
  rw [hsplit]
  split_ifs with h0
  · subst h0
    simp only [pow_zero, one_pow, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
    ring
  · have hne : ζ ^ n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt h0 hn
    have hpow : (ζ ^ n) ^ M = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, mul_zero, zero_sub]

/-- `thm:quadrature`: the weights are positive when `0 < ε` and `(M - 1)ε < 1`. -/
theorem quadratureWeight_pos [LinearOrder F] [IsStrictOrderedRing F] {M : ℕ} (hM : 0 < M)
    {ε : F} (hε : 0 < ε) (hMε : (M - 1) * ε < 1) (k : ℕ) : 0 < quadratureWeight M ε k := by
  have hM' : (0 : F) < M := by exact_mod_cast hM
  rw [quadratureWeight]
  split_ifs
  · rw [sub_pos, lt_div_iff₀ hM']
    nlinarith
  · simpa using div_pos (by linarith) hM'

end Quadrature

end

end Surreal.Herglotz
