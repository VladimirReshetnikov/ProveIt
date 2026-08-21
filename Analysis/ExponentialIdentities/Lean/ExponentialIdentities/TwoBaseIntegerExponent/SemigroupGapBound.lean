import ExponentialIdentities.TwoBaseIntegerExponent.ArbitraryNodeDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.ExponentialPolynomialZeros
import ExponentialIdentities.TwoBaseIntegerExponent.FallingFactorialBound
import ExponentialIdentities.TwoBaseIntegerExponent.SemigroupDeterminant
import ExponentialIdentities.TwoBaseIntegerExponent.SemigroupWeightBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Interval.Finset.Fin

/-!
# The quantitative semigroup gap theorem and its dyadic `O((log X)^2)` bound

This module assembles the five previously accepted layers of the semigroup generalized
Vandermonde chain of the Alaoglu--Erdős unified report, Section "New result II: semigroup
generalized Vandermonde determinants", into the quantitative gap theorem
`sg:thm-semigroup-gap` and the explicit counting corollaries
`sg:cor-explicit-semigroup-span`, `sg:cor-semigroup-interval-count` and
`sg:cor-semigroup-log-square`.

The layers already in the repository are

* `MixedExponentSemigroup`: the exponent semigroup `Λ_θ = {a + b θ : a, b ∈ ℕ}` and mixed
  integrality `m ^ (a + b θ) ∈ ℕ` for a natural candidate `m`;
* `SemigroupDeterminant`: `semigroupMatrix` and the integrality lower bound `1 ≤ |det|` for
  a nonvanishing determinant;
* `ExponentialPolynomialZeros`: nonvanishing of `det (xᵢ ^ λⱼ)` for strictly increasing
  positive nodes and strictly increasing real exponents;
* `FallingFactorialBound`: `|(λ)_i| / i ! * x ^ (λ - i) ≤ 2 ^ (2 λ + i) * N ^ (λ - i)` on the
  dyadic strip `[N, 2N]`;
* `SemigroupWeightBound`: the crude weight bound `Σ_r ≤ 6 (r+1) √r` and the
  window-span-to-cardinality pigeonhole bridge.

## What is proved here

* `abs_det_le_of_abs_entry_le` — the **Leibniz determinant bound**: if `|M i j| ≤ A i * B j`
  entrywise, then `|det M| ≤ (card)! * (∏ A) * (∏ B)`.  This is the missing reusable
  estimate; it is proved from the Leibniz formula `Matrix.det_apply'`, and needs no
  hypothesis at all beyond the entrywise bound (which already forces `A i * B j ≥ 0`).
* `det_semigroupMatrix_ne_zero` — the semigroup matrix of strictly increasing positive nodes
  and strictly increasing exponents is *literally* the generalized Vandermonde matrix of
  `ExponentialPolynomialZeros`, so its determinant is nonzero.  This removes the positivity
  hypothesis that `SemigroupDeterminant.one_le_det_semigroupMatrix` had to assume.
* `abs_det_dividedDifference_le` — the Leibniz bound applied to the Newton
  divided-difference matrix, giving `|det dd| ≤ (r+1)! * 2 ^ (R + 2 Σ) * N ^ (Σ - R)`.
* `one_le_span_pow_mul` and `span_lower_bound` — the **semigroup determinant gap**, in a
  root-free power form and in the report's form
  `H ≥ ((r+1)!) ^ (-1/R) * 2 ^ (-1 - 2 Σ/R) * N ^ (1 - Σ/R)`.
* `explicit_span_lower_bound`, `card_le_of_semigroup_span`,
  `card_le_ten_thousand_log_sq` and `card_le_ten_thousand_max_log_sq` — the explicit
  `r ≥ 144` span bound `H ≥ N ^ (1 - 12/√r)/24`, the interval count
  `#S ≤ r + 24 r H N ^ (-1 + 12/√r)`, and the dyadic bound
  `#(Cand ∩ [X, 2X]) ≤ 10000 max(1, log X) ^ 2`.

## The Newton divided-difference hypothesis

The report's factorization `D_λ(m) = V(m) det (f_j[m_0, …, m_i])` (equation
`sg:eq-newton-factorization`) together with the mean-value bound `sg:eq-dd-first-bound` is
*analytic input* developed separately.  It enters here as the explicit hypothesis
`NewtonFactorization`, exactly as `ArbitraryNodeDeterminant.lean` takes its
determinant/divided-difference factorization as a hypothesis.  Everything downstream of that
hypothesis is proved.

No separate strip hypothesis `N + H ≤ 2 N` is needed: the strip enters only through the
location `ξ ∈ [N, 2N]` of the mean-value point, which is part of `NewtonRowBound`.
-/

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### The pair count `R_r = r (r + 1) / 2` -/

/-- `R_r = ∑_{i=0}^{r} i = r (r + 1) / 2`.  It is simultaneously the total row weight of the
Newton divided-difference matrix (row `i` contributes the factor `N ^ (-i)`) and the number
of node pairs occurring in the Vandermonde product. -/
def semigroupR (r : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), i

/-- Gauss summation: `2 R_r = (r + 1) r`. -/
theorem semigroupR_mul_two (r : ℕ) : semigroupR r * 2 = (r + 1) * r := by
  simpa [semigroupR] using Finset.sum_range_id_mul_two (r + 1)

/-- `R_r` is positive as soon as `r ≥ 1`. -/
theorem semigroupR_pos {r : ℕ} (hr : 1 ≤ r) : 0 < semigroupR r := by
  have h1 : (1 : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hle : (1 : ℕ) ≤ ∑ i ∈ Finset.range (r + 1), i :=
    Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) h1
  show 0 < ∑ i ∈ Finset.range (r + 1), i
  exact lt_of_lt_of_le Nat.zero_lt_one hle

/-- The real value of `R_r` is `r (r + 1) / 2`. -/
theorem semigroupR_cast (r : ℕ) :
    ((semigroupR r : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
  have h : semigroupR r * 2 = (r + 1) * r := semigroupR_mul_two r
  have h' : ((semigroupR r : ℕ) : ℝ) * 2 = ((r : ℝ) + 1) * (r : ℝ) := by exact_mod_cast h
  linarith

/-- The total row weight `∑_{i=0}^{r} i`, computed over `Fin (r + 1)`. -/
theorem sum_natCast_fin (r : ℕ) :
    (∑ i : Fin (r + 1), ((i : ℕ) : ℝ)) = ((semigroupR r : ℕ) : ℝ) := by
  have h1 : (∑ i : Fin (r + 1), ((i : ℕ) : ℝ))
      = ∑ i ∈ Finset.range (r + 1), (i : ℝ) :=
    (Finset.sum_range (n := r + 1) fun i : ℕ => (i : ℝ)).symm
  have h2 : ((semigroupR r : ℕ) : ℝ) = ∑ i ∈ Finset.range (r + 1), (i : ℝ) := by
    show ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) = _
    exact Nat.cast_sum _ _
  rw [h1, h2]

/-- The number of ordered node pairs `i < j` in `Fin (r + 1)` is `R_r`. -/
theorem sum_card_Ioi_fin (r : ℕ) :
    (∑ i : Fin (r + 1), (Finset.Ioi i).card) = semigroupR r := by
  have h1 : (∑ i : Fin (r + 1), (Finset.Ioi i).card)
      = ∑ i ∈ Finset.range (r + 1), (r + 1 - 1 - i) := by
    rw [Finset.sum_range (n := r + 1) fun i : ℕ => r + 1 - 1 - i]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.card_Ioi]
  rw [h1]
  show (∑ i ∈ Finset.range (r + 1), (r + 1 - 1 - i)) = ∑ i ∈ Finset.range (r + 1), i
  exact Finset.sum_range_reflect (fun i : ℕ => i) (r + 1)

noncomputable section

/-! ### The Leibniz determinant bound

This is the estimate the semigroup chain was missing.  It is completely general: no ordering,
positivity or integrality of the entries is used, only the separated entrywise bound. -/

/-- **Leibniz determinant bound.**  If every entry of a square real matrix satisfies
`|M i j| ≤ A i * B j`, then

`|det M| ≤ (Fintype.card ι)! * ((∏ i, A i) * (∏ j, B j))`.

Each Leibniz term `sign σ * ∏ i, M (σ i) i` has absolute value at most
`∏ i, (A (σ i) * B i) = (∏ A) * (∏ B)`, because reindexing the row factors by the permutation
`σ` leaves `∏ A` unchanged; there are `(Fintype.card ι)!` such terms.  No sign hypothesis on
`A` and `B` is needed: the entrywise bound already forces `A i * B j ≥ 0`. -/
theorem abs_det_le_of_abs_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (A B : ι → ℝ) (h : ∀ i j, |M i j| ≤ A i * B j) :
    |M.det| ≤ ((Fintype.card ι)! : ℝ) * ((∏ i, A i) * ∏ j, B j) := by
  have key : ∀ σ : Equiv.Perm ι,
      |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i| ≤ (∏ i, A i) * ∏ j, B j := by
    intro σ
    have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [abs_mul, hsign, one_mul, Finset.abs_prod]
    calc (∏ i, |M (σ i) i|)
        ≤ ∏ i, A (σ i) * B i :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => h (σ i) i)
      _ = (∏ i, A (σ i)) * ∏ i, B i := Finset.prod_mul_distrib
      _ = (∏ i, A i) * ∏ j, B j := by rw [Equiv.prod_comp σ A]
  calc |M.det|
      = |∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i| := by
        rw [Matrix.det_apply']
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ((∏ i, A i) * ∏ j, B j) :=
        Finset.sum_le_sum fun σ _ => key σ
    _ = ((Fintype.card ι)! : ℝ) * ((∏ i, A i) * ∏ j, B j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-! ### Two elementary `rpow` computations -/

/-- A finite product of real powers of a fixed positive base is the power of the sum. -/
theorem prod_rpow_eq_rpow_sum {ι : Type*} (s : Finset ι) {x : ℝ} (hx : 0 < x) (f : ι → ℝ) :
    (∏ i ∈ s, x ^ f i) = x ^ (∑ i ∈ s, f i) := by
  simp only [Real.rpow_def_of_pos hx]
  rw [← Real.exp_sum, ← Finset.mul_sum]

/-- The divided-difference bound `2 ^ (2 λ + i) * N ^ (λ - i)` splits as a row factor
depending only on `i` times a column factor depending only on `λ`.  This is exactly the
separated shape the Leibniz estimate consumes. -/
theorem two_pow_mul_rpow_factor {N : ℝ} (hN : 0 < N) (lam : ℝ) (i : ℕ) :
    (2 : ℝ) ^ (2 * lam + (i : ℝ)) * N ^ (lam - (i : ℝ))
      = ((2 : ℝ) ^ (i : ℝ) * N ^ (-(i : ℝ))) * ((2 : ℝ) ^ (2 * lam) * N ^ lam) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_sub hN, Real.rpow_neg hN.le,
    div_eq_mul_inv]
  ring

/-! ### Nonvanishing of the semigroup determinant -/

/-- The semigroup generalized Vandermonde matrix *is* the `rpow` Vandermonde matrix on the
nodes `m i` with the exponents `mixedExponent (ab j)`. -/
theorem semigroupMatrix_eq_rpowVandermonde (r : ℕ) (m : Fin (r + 1) → ℕ)
    (ab : Fin (r + 1) → ℕ × ℕ) :
    semigroupMatrix r m ab
      = rpowVandermonde (fun i => ((m i : ℕ) : ℝ)) (fun j => mixedExponent (ab j)) :=
  rfl

/-- **The semigroup determinant does not vanish.**  For strictly increasing positive natural
nodes and strictly increasing mixed exponents, `det (m i ^ λ_j) ≠ 0`.  This is the zero-count
theorem for exponential polynomials of `ExponentialPolynomialZeros.lean`, and it replaces the
positivity hypothesis of `SemigroupDeterminant.one_le_det_semigroupMatrix`. -/
theorem det_semigroupMatrix_ne_zero (r : ℕ) (m : Fin (r + 1) → ℕ)
    (ab : Fin (r + 1) → ℕ × ℕ) (hm : StrictMono m) (hm0 : 0 < m 0)
    (hlam : StrictMono fun j => mixedExponent (ab j)) :
    (semigroupMatrix r m ab).det ≠ 0 := by
  rw [semigroupMatrix_eq_rpowVandermonde]
  refine det_rpowVandermonde_ne_zero _ _ ?_ ?_ hlam
  · intro a b hab
    show ((m a : ℕ) : ℝ) < ((m b : ℕ) : ℝ)
    exact_mod_cast hm hab
  · show (0 : ℝ) < ((m 0 : ℕ) : ℝ)
    exact_mod_cast hm0

/-! ### The divided-difference determinant bound -/

/-- The mean-value bound `sg:eq-dd-first-bound`, rewritten in the separated form
`|dd i j| ≤ A i * B j` required by the Leibniz estimate.  The rewriting is the
falling-factorial bound of `FallingFactorialBound.lean`. -/
theorem abs_le_row_col_bound {N : ℝ} (hN : 1 ≤ N) {lam : ℝ} (hlam : 0 ≤ lam)
    {ξ y : ℝ} (h1 : N ≤ ξ) (h2 : ξ ≤ 2 * N) (i : ℕ)
    (hy : |y| ≤ |fallingRpowCoeff lam i| / (i ! : ℝ) * ξ ^ (lam - (i : ℝ))) :
    |y| ≤ ((2 : ℝ) ^ (i : ℝ) * N ^ (-(i : ℝ))) * ((2 : ℝ) ^ (2 * lam) * N ^ lam) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hbound := abs_fallingRpowCoeff_div_factorial_mul_rpow_le hN h1 h2 hlam i
  rw [← two_pow_mul_rpow_factor hNpos lam i]
  exact hy.trans hbound

/-- **The divided-difference determinant bound.**  If every entry of the Newton
divided-difference matrix obeys the mean-value bound `sg:eq-dd-first-bound` on the dyadic
strip `[N, 2N]`, then

`|det dd| ≤ (r + 1)! * 2 ^ (R + 2 Σ) * N ^ (Σ - R)`,

with `R = R_r = r (r + 1) / 2` and `Σ = ∑_j λ_j`.  This is the Leibniz bound applied with
the row factor `2 ^ i * N ^ (-i)` and the column factor `2 ^ (2 λ_j) * N ^ (λ_j)`; the two
products are evaluated by `prod_rpow_eq_rpow_sum` and `sum_natCast_fin`. -/
theorem abs_det_dividedDifference_le (r : ℕ) (lam : Fin (r + 1) → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) {N : ℝ} (hN : 1 ≤ N)
    (dd : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (hdd : ∀ i j : Fin (r + 1), ∃ ξ : ℝ, N ≤ ξ ∧ ξ ≤ 2 * N ∧
      |dd i j| ≤ |fallingRpowCoeff (lam j) (i : ℕ)| / ((i : ℕ)! : ℝ)
        * ξ ^ (lam j - ((i : ℕ) : ℝ))) :
    |dd.det| ≤ (((r + 1)! : ℕ) : ℝ)
      * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, lam j)
        * N ^ ((∑ j, lam j) - ((semigroupR r : ℕ) : ℝ))) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hentry : ∀ i j : Fin (r + 1),
      |dd i j| ≤ ((2 : ℝ) ^ ((i : ℕ) : ℝ) * N ^ (-((i : ℕ) : ℝ)))
        * ((2 : ℝ) ^ (2 * lam j) * N ^ lam j) := by
    intro i j
    obtain ⟨ξ, h1, h2, h3⟩ := hdd i j
    exact abs_le_row_col_bound hN (hlam j) h1 h2 (i : ℕ) h3
  have hdet : |dd.det| ≤ (((r + 1)! : ℕ) : ℝ)
      * ((∏ i : Fin (r + 1), ((2 : ℝ) ^ ((i : ℕ) : ℝ) * N ^ (-((i : ℕ) : ℝ))))
        * ∏ j : Fin (r + 1), ((2 : ℝ) ^ (2 * lam j) * N ^ lam j)) := by
    have h := abs_det_le_of_abs_entry_le dd
      (fun i : Fin (r + 1) => (2 : ℝ) ^ ((i : ℕ) : ℝ) * N ^ (-((i : ℕ) : ℝ)))
      (fun j : Fin (r + 1) => (2 : ℝ) ^ (2 * lam j) * N ^ lam j) hentry
    rwa [Fintype.card_fin] at h
  have hprodA :
      (∏ i : Fin (r + 1), ((2 : ℝ) ^ ((i : ℕ) : ℝ) * N ^ (-((i : ℕ) : ℝ))))
        = (2 : ℝ) ^ ((semigroupR r : ℕ) : ℝ) * N ^ (-((semigroupR r : ℕ) : ℝ)) := by
    rw [Finset.prod_mul_distrib,
      prod_rpow_eq_rpow_sum (Finset.univ : Finset (Fin (r + 1)))
        (by norm_num : (0 : ℝ) < 2) (fun i : Fin (r + 1) => ((i : ℕ) : ℝ)),
      prod_rpow_eq_rpow_sum (Finset.univ : Finset (Fin (r + 1))) hNpos
        (fun i : Fin (r + 1) => -((i : ℕ) : ℝ)),
      Finset.sum_neg_distrib, sum_natCast_fin r]
  have hprodB :
      (∏ j : Fin (r + 1), ((2 : ℝ) ^ (2 * lam j) * N ^ lam j))
        = (2 : ℝ) ^ (2 * ∑ j, lam j) * N ^ (∑ j, lam j) := by
    rw [Finset.prod_mul_distrib,
      prod_rpow_eq_rpow_sum (Finset.univ : Finset (Fin (r + 1)))
        (by norm_num : (0 : ℝ) < 2) (fun j : Fin (r + 1) => 2 * lam j),
      prod_rpow_eq_rpow_sum (Finset.univ : Finset (Fin (r + 1))) hNpos
        (fun j : Fin (r + 1) => lam j),
      ← Finset.mul_sum]
  have hcombine :
      ((2 : ℝ) ^ ((semigroupR r : ℕ) : ℝ) * N ^ (-((semigroupR r : ℕ) : ℝ)))
          * ((2 : ℝ) ^ (2 * ∑ j, lam j) * N ^ (∑ j, lam j))
        = (2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, lam j)
          * N ^ ((∑ j, lam j) - ((semigroupR r : ℕ) : ℝ)) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_sub hNpos,
      Real.rpow_neg hNpos.le, div_eq_mul_inv]
    ring
  rw [hprodA, hprodB, hcombine] at hdet
  exact hdet

/-! ### The Vandermonde factor on a window of width `H` -/

/-- **The Vandermonde product of a window.**  If every pairwise node difference is at most
`H`, the Vandermonde product `∏_{i<j} (m j - m i)` is at most `H ^ R_r`, because there are
exactly `R_r = r (r + 1) / 2` node pairs. -/
theorem vandermondeProduct_le_pow_semigroupR (r : ℕ) (m : Fin (r + 1) → ℕ) (hm : StrictMono m)
    {H : ℝ} (hH : ∀ i j : Fin (r + 1), i < j → (m j : ℝ) - (m i : ℝ) ≤ H) :
    vandermondeProduct r m ≤ H ^ semigroupR r := by
  have hpos : ∀ i j : Fin (r + 1), i < j → (0 : ℝ) ≤ (m j : ℝ) - (m i : ℝ) := by
    intro i j hij
    have hlt : ((m i : ℕ) : ℝ) < ((m j : ℕ) : ℝ) := by exact_mod_cast hm hij
    linarith
  have hinner0 : ∀ i : Fin (r + 1),
      (0 : ℝ) ≤ ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)) := fun i =>
    Finset.prod_nonneg fun j hj => hpos i j (Finset.mem_Ioi.mp hj)
  have hinner : ∀ i : Fin (r + 1),
      (∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ))) ≤ H ^ (Finset.Ioi i).card := by
    intro i
    calc (∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)))
        ≤ ∏ _j ∈ Finset.Ioi i, H :=
          Finset.prod_le_prod (fun j hj => hpos i j (Finset.mem_Ioi.mp hj))
            (fun j hj => hH i j (Finset.mem_Ioi.mp hj))
      _ = H ^ (Finset.Ioi i).card := Finset.prod_const H
  show (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)))
      ≤ H ^ semigroupR r
  calc (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, ((m j : ℝ) - (m i : ℝ)))
      ≤ ∏ i : Fin (r + 1), H ^ (Finset.Ioi i).card :=
        Finset.prod_le_prod (fun i _ => hinner0 i) (fun i _ => hinner i)
    _ = H ^ (∑ i : Fin (r + 1), (Finset.Ioi i).card) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = H ^ semigroupR r := by rw [sum_card_Ioi_fin r]

/-! ### The Newton divided-difference hypothesis -/

/-- **The Newton row bound** of the report's `sg:eq-dd-first-bound`.  Entry `(i, j)` of the
divided-difference matrix is the divided difference of `x ↦ x ^ λ_j` over the nodes
`m 0, …, m i`, and the generalized mean-value theorem produces a point `ξ` of the dyadic
strip `[N, 2N]` with `|dd i j| ≤ |(λ_j)_i| / i ! * ξ ^ (λ_j - i)`.

This module does not prove that such a matrix exists; it consumes the statement. -/
def NewtonRowBound (r : ℕ) (ab : Fin (r + 1) → ℕ × ℕ) (N : ℝ)
    (dd : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) : Prop :=
  ∀ i j : Fin (r + 1), ∃ ξ : ℝ, N ≤ ξ ∧ ξ ≤ 2 * N ∧
    |dd i j| ≤ |fallingRpowCoeff (mixedExponent (ab j)) (i : ℕ)| / ((i : ℕ)! : ℝ)
      * ξ ^ (mixedExponent (ab j) - ((i : ℕ) : ℝ))

/-- **The Newton divided-difference factorization** of the report's
`sg:eq-newton-factorization`, together with the row bound: the semigroup determinant factors
as the Vandermonde product of the nodes times the determinant of a matrix of divided
differences, each obeying the mean-value bound on `[N, 2N]`.

This is the single analytic input of the chain below; every statement downstream of it is
proved here.  It is the exact analogue of the hypothesis taken by
`ArbitraryNodeDeterminant.one_le_vandermondeProduct_mul_of_dividedDifference`. -/
def NewtonFactorization (r : ℕ) (m : Fin (r + 1) → ℕ) (ab : Fin (r + 1) → ℕ × ℕ)
    (N : ℝ) : Prop :=
  ∃ dd : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ,
    (semigroupMatrix r m ab).det = vandermondeProduct r m * dd.det ∧
    NewtonRowBound r ab N dd

/-! ### The quantitative semigroup gap theorem -/

/-- **Semigroup determinant gap, power form.**  For `r + 1` natural candidates in
`[N, N + H]` with `N ≥ 1`, strictly increasing mixed exponents, and the Newton
divided-difference input,

`1 ≤ H ^ R * ((r + 1)! * 2 ^ (R + 2 Σ) * N ^ (Σ - R))`,

which is the chain `1 ≤ D_λ(m) ≤ H ^ R (r+1)! 2 ^ (R + 2 Σ) N ^ (Σ - R)` in the report's
proof of `sg:thm-semigroup-gap`.  The lower bound `1` is integrality plus nonvanishing; the
upper bound is the Vandermonde window bound times the Leibniz estimate. -/
theorem one_le_span_pow_mul (r : ℕ) (m : Fin (r + 1) → ℕ) (ab : Fin (r + 1) → ℕ × ℕ)
    (hm : StrictMono m) (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hlam : StrictMono fun j => mixedExponent (ab j))
    {N H : ℝ} (hN : 1 ≤ N) (hlow : ∀ i, N ≤ (m i : ℝ)) (hhigh : ∀ i, (m i : ℝ) ≤ N + H)
    (hfact : NewtonFactorization r m ab N) :
    1 ≤ H ^ semigroupR r * ((((r + 1)! : ℕ) : ℝ)
      * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
        * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ)))) := by
  obtain ⟨dd, hdetfac, hrow⟩ := hfact
  have hH0 : 0 ≤ H := by
    have h1 := hlow 0
    have h2 := hhigh 0
    linarith
  have hne : (semigroupMatrix r m ab).det ≠ 0 :=
    det_semigroupMatrix_ne_zero r m ab hm (hcand 0).1 hlam
  have hone : (1 : ℝ) ≤ |(semigroupMatrix r m ab).det| :=
    one_le_abs_det_semigroupMatrix r m hcand ab hne
  have hV : 0 < vandermondeProduct r m := vandermondeProduct_pos r m hm
  have hVle : vandermondeProduct r m ≤ H ^ semigroupR r := by
    refine vandermondeProduct_le_pow_semigroupR r m hm ?_
    intro i j _
    have h1 := hlow i
    have h2 := hhigh j
    linarith
  have hddle := abs_det_dividedDifference_le r (fun j => mixedExponent (ab j))
    (fun j => mixedExponent_nonneg (ab j)) hN dd hrow
  calc (1 : ℝ) ≤ |(semigroupMatrix r m ab).det| := hone
    _ = vandermondeProduct r m * |dd.det| := by rw [hdetfac, abs_mul, abs_of_pos hV]
    _ ≤ H ^ semigroupR r * ((((r + 1)! : ℕ) : ℝ)
        * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
          * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ)))) :=
        mul_le_mul hVle hddle (abs_nonneg _) (pow_nonneg hH0 _)

/-- Taking `R`-th roots in an inequality `1 ≤ H ^ R * K`. -/
theorem rpow_neg_inv_le_of_one_le_pow_mul {H K : ℝ} {R : ℕ} (hR : R ≠ 0)
    (hH : 0 ≤ H) (hK : 0 < K) (h : 1 ≤ H ^ R * K) :
    K ^ (-(1 / (R : ℝ))) ≤ H := by
  have hRne : ((R : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR
  have hinv : K⁻¹ ≤ H ^ R := by
    have h' := mul_le_mul_of_nonneg_right h (inv_pos.mpr hK).le
    rw [one_mul, mul_assoc, mul_inv_cancel₀ hK.ne', mul_one] at h'
    exact h'
  have h1 : (K⁻¹) ^ (1 / (R : ℝ)) ≤ (H ^ R) ^ (1 / (R : ℝ)) :=
    Real.rpow_le_rpow (inv_nonneg.mpr hK.le) hinv (by positivity)
  have h2 : ((H ^ R : ℝ)) ^ (1 / (R : ℝ)) = H := by
    rw [← Real.rpow_natCast H R, ← Real.rpow_mul hH, mul_one_div, div_self hRne,
      Real.rpow_one]
  have h3 : (K⁻¹) ^ (1 / (R : ℝ)) = K ^ (-(1 / (R : ℝ))) := by
    rw [Real.inv_rpow hK.le, ← Real.rpow_neg hK.le]
  rw [h2, h3] at h1
  exact h1

/-- The `R`-th root of `c * (2 ^ (R + 2 S) * N ^ (S - R))`, in the report's normalized
form `c ^ (-1/R) * 2 ^ (-1 - 2 S/R) * N ^ (1 - S/R)`. -/
theorem rpow_neg_inv_mul_eq {c : ℝ} (hc : 0 < c) {N : ℝ} (hN : 0 < N) {R S : ℝ}
    (hR : R ≠ 0) :
    (c * ((2 : ℝ) ^ (R + 2 * S) * N ^ (S - R))) ^ (-(1 / R))
      = c ^ (-(1 / R)) * (2 : ℝ) ^ (-1 - 2 * S / R) * N ^ (1 - S / R) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (R + 2 * S) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0 : ℝ) < N ^ (S - R) := Real.rpow_pos_of_pos hN _
  have hexp2 : (R + 2 * S) * (-(1 / R)) = -1 - 2 * S / R := by
    have h : (R + 2 * S) * (-(1 / R)) = -(R / R) - 2 * S / R := by ring
    rw [h, div_self hR]
  have hexpN : (S - R) * (-(1 / R)) = 1 - S / R := by
    have h : (S - R) * (-(1 / R)) = R / R - S / R := by ring
    rw [h, div_self hR]
  rw [Real.mul_rpow hc.le (mul_pos h2 h3).le, Real.mul_rpow h2.le h3.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hN.le, hexp2, hexpN]
  ring

/-- **Semigroup determinant gap** (`sg:thm-semigroup-gap`).  Let `r ≥ 1`, let
`λ_0 < ⋯ < λ_r` be mixed exponents of `Λ_θ`, and put `R = r (r + 1) / 2`, `Σ = ∑_j λ_j`.  If
`r + 1` natural candidates lie in `[N, N + H]` with `N ≥ 1`, and the Newton
divided-difference input holds, then

`H ≥ ((r + 1)!) ^ (-1/R) * 2 ^ (-1 - 2 Σ/R) * N ^ (1 - Σ/R)`. -/
theorem span_lower_bound (r : ℕ) (hr : 1 ≤ r) (m : Fin (r + 1) → ℕ)
    (ab : Fin (r + 1) → ℕ × ℕ) (hm : StrictMono m)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hlam : StrictMono fun j => mixedExponent (ab j))
    {N H : ℝ} (hN : 1 ≤ N) (hlow : ∀ i, N ≤ (m i : ℝ)) (hhigh : ∀ i, (m i : ℝ) ≤ N + H)
    (hfact : NewtonFactorization r m ab N) :
    (((r + 1)! : ℕ) : ℝ) ^ (-(1 / ((semigroupR r : ℕ) : ℝ)))
        * (2 : ℝ) ^ (-1 - 2 * (∑ j, mixedExponent (ab j)) / ((semigroupR r : ℕ) : ℝ))
        * N ^ (1 - (∑ j, mixedExponent (ab j)) / ((semigroupR r : ℕ) : ℝ)) ≤ H := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hR0 : semigroupR r ≠ 0 := (semigroupR_pos hr).ne'
  have hRne : ((semigroupR r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hR0
  have hH0 : 0 ≤ H := by
    have h1 := hlow 0
    have h2 := hhigh 0
    linarith
  have hc : (0 : ℝ) < (((r + 1)! : ℕ) : ℝ) := by
    have hpos := (r + 1).factorial_pos
    exact_mod_cast hpos
  have hK : (0 : ℝ) < (((r + 1)! : ℕ) : ℝ)
      * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
        * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))) :=
    mul_pos hc (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hNpos _))
  have hmain := one_le_span_pow_mul r m ab hm hcand hlam hN hlow hhigh hfact
  have hkey := rpow_neg_inv_le_of_one_le_pow_mul hR0 hH0 hK hmain
  rwa [rpow_neg_inv_mul_eq hc hNpos hRne] at hkey

/-! ### The explicit `r ≥ 144` form -/

/-- `(n + 1) ^ 2 ≤ 3 ^ n` for `n ≥ 2`; the elementary input to `(r + 1)! ≤ 3 ^ R_r`. -/
theorem succ_sq_le_three_pow : ∀ n : ℕ, 2 ≤ n → (n + 1) ^ 2 ≤ 3 ^ n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge k 2 with hk | hk
      · have hk1 : k = 1 := by omega
        subst hk1
        norm_num
      · have hprev := ih hk
        have hstep : (k + 1 + 1) ^ 2 ≤ 3 * (k + 1) ^ 2 := by nlinarith [hk]
        calc (k + 1 + 1) ^ 2 ≤ 3 * (k + 1) ^ 2 := hstep
          _ ≤ 3 * 3 ^ k := Nat.mul_le_mul (le_refl 3) hprev
          _ = 3 ^ (k + 1) := by ring

/-- `(r + 1)! ≤ 3 ^ R_r` for `r ≥ 2`.  This is the report's estimate
`((r+1)!) ^ (1/R) ≤ (r+1) ^ (2/r) ≤ 3`, squared so that only natural-number arithmetic is
needed: `((r+1)!) ^ 2 ≤ ((r+1) ^ 2) ^ (r+1) ≤ 3 ^ (r (r+1)) = (3 ^ R) ^ 2`. -/
theorem factorial_le_three_pow {r : ℕ} (hr : 2 ≤ r) : (r + 1)! ≤ 3 ^ semigroupR r := by
  have hfac : (r + 1)! ≤ (r + 1) ^ (r + 1) := Nat.factorial_le_pow (r + 1)
  have hsq : (r + 1) ^ 2 ≤ 3 ^ r := succ_sq_le_three_pow r hr
  have hRm : semigroupR r * 2 = (r + 1) * r := semigroupR_mul_two r
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have key : ((r + 1)!) ^ 2 ≤ (3 ^ semigroupR r) ^ 2 := by
    calc ((r + 1)!) ^ 2 ≤ ((r + 1) ^ (r + 1)) ^ 2 := Nat.pow_le_pow_left hfac 2
      _ = ((r + 1) ^ 2) ^ (r + 1) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm (r + 1) 2]
      _ ≤ (3 ^ r) ^ (r + 1) := Nat.pow_le_pow_left hsq (r + 1)
      _ = 3 ^ (r * (r + 1)) := (pow_mul 3 r (r + 1)).symm
      _ = 3 ^ (semigroupR r * 2) := by rw [hRm, Nat.mul_comm r (r + 1)]
      _ = (3 ^ semigroupR r) ^ 2 := pow_mul 3 (semigroupR r) 2
  exact (Nat.pow_le_pow_iff_left h2).mp key

/-- The real form of `factorial_le_three_pow`. -/
theorem factorial_le_three_pow_real {r : ℕ} (hr : 2 ≤ r) :
    (((r + 1)! : ℕ) : ℝ) ≤ (3 : ℝ) ^ semigroupR r := by
  have h := factorial_le_three_pow hr
  exact_mod_cast h

/-- For `r ≥ 144` the square root of `r` is at least `12`, so the exponent deficit `12 / √r`
of the crude weight bound is at most `1`. -/
theorem twelve_le_sqrt {r : ℕ} (hr : 144 ≤ r) : (12 : ℝ) ≤ Real.sqrt (r : ℝ) := by
  refine Real.le_sqrt_of_sq_le ?_
  have h : (144 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  calc (12 : ℝ) ^ 2 = 144 := by norm_num
    _ ≤ (r : ℝ) := h

/-- `R_r * (12 / √r) = 6 (r + 1) √r`: the crude weight bound of `SemigroupWeightBound.lean`
is exactly the report's `Σ_r / R_r ≤ 12 / √r` from `sg:eq-crude-semigroup`. -/
theorem semigroupR_mul_twelve_div_sqrt {r : ℕ} (hr : 1 ≤ r) :
    ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ))
      = 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
  have hspos : (0 : ℝ) < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hss : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) := Real.mul_self_sqrt hrR.le
  have hkey : (r : ℝ) * ((r : ℝ) + 1) / 2 * 12
      = (6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ)) * Real.sqrt (r : ℝ) := by
    rw [mul_assoc (6 * ((r : ℝ) + 1)), hss]
    ring
  rw [semigroupR_cast r]
  calc (r : ℝ) * ((r : ℝ) + 1) / 2 * (12 / Real.sqrt (r : ℝ))
      = ((r : ℝ) * ((r : ℝ) + 1) / 2 * 12) / Real.sqrt (r : ℝ) := by ring
    _ = ((6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ)) * Real.sqrt (r : ℝ))
          / Real.sqrt (r : ℝ) := by rw [hkey]
    _ = 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by
        rw [mul_div_assoc, div_self hspos.ne', mul_one]

/-- **Explicit near-linear span** (`sg:cor-explicit-semigroup-span`).  For `r ≥ 144`, `r + 1`
natural candidates in `[N, N + H]` with `N ≥ 1`, whose mixed exponents are strictly
increasing and obey the crude weight bound `Σ ≤ 6 (r + 1) √r`, satisfy

`H ≥ N ^ (1 - 12 / √r) / 24`.

The proof is the root-free form of the report's argument.  Were `H` smaller, then
`H ^ R * ((r+1)! * 2 ^ (R + 2 Σ) * N ^ (Σ - R))` would be strictly below `1`, because
`(r+1)! ≤ 3 ^ R`, `2 ^ (R + 2 Σ) ≤ 8 ^ R` (which needs `Σ ≤ R`, i.e. `12/√r ≤ 1`),
`N ^ (Σ - 12 R/√r) ≤ 1` and `3 ^ R * 8 ^ R = 24 ^ R`. -/
theorem explicit_span_lower_bound (r : ℕ) (hr : 144 ≤ r) (m : Fin (r + 1) → ℕ)
    (ab : Fin (r + 1) → ℕ × ℕ) (hm : StrictMono m)
    (hcand : ∀ i, TwoBaseNaturalCandidate (m i))
    (hlam : StrictMono fun j => mixedExponent (ab j))
    (hsum : (∑ j, mixedExponent (ab j)) ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ))
    {N H : ℝ} (hN : 1 ≤ N) (hlow : ∀ i, N ≤ (m i : ℝ)) (hhigh : ∀ i, (m i : ℝ) ≤ N + H)
    (hfact : NewtonFactorization r m ab N) :
    N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24 ≤ H := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hs12 : (12 : ℝ) ≤ Real.sqrt (r : ℝ) := twelve_le_sqrt hr
  have hspos : (0 : ℝ) < Real.sqrt (r : ℝ) := lt_of_lt_of_le (by norm_num) hs12
  have hRpos : 0 < semigroupR r := semigroupR_pos hr1
  have hRposR : (0 : ℝ) < ((semigroupR r : ℕ) : ℝ) := by exact_mod_cast hRpos
  have hid := semigroupR_mul_twelve_div_sqrt hr1
  have h12s : (12 : ℝ) / Real.sqrt (r : ℝ) ≤ 1 := by
    rw [div_le_one hspos]
    exact hs12
  have hSigR : (∑ j, mixedExponent (ab j)) ≤ ((semigroupR r : ℕ) : ℝ) := by
    calc (∑ j, mixedExponent (ab j))
        ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := hsum
      _ = ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ)) := hid.symm
      _ ≤ ((semigroupR r : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h12s hRposR.le
      _ = ((semigroupR r : ℕ) : ℝ) := mul_one _
  have hH0 : 0 ≤ H := by
    have h1 := hlow 0
    have h2 := hhigh 0
    linarith
  have hmain := one_le_span_pow_mul r m ab hm hcand hlam hN hlow hhigh hfact
  have h3bound : (((r + 1)! : ℕ) : ℝ) ≤ (3 : ℝ) ^ semigroupR r :=
    factorial_le_three_pow_real hr2
  have h2bound : (2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
      ≤ (8 : ℝ) ^ semigroupR r := by
    have hle : ((semigroupR r : ℕ) : ℝ) + 2 * (∑ j, mixedExponent (ab j))
        ≤ ((3 * semigroupR r : ℕ) : ℝ) := by
      push_cast
      linarith [hSigR]
    calc (2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
        ≤ (2 : ℝ) ^ (((3 * semigroupR r : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = (2 : ℝ) ^ (3 * semigroupR r) := Real.rpow_natCast 2 (3 * semigroupR r)
      _ = (8 : ℝ) ^ semigroupR r := by rw [pow_mul]; norm_num
  have hexpnp : (∑ j, mixedExponent (ab j))
      - ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ)) ≤ 0 := by
    rw [hid]
    linarith [hsum]
  have hNle1 : N ^ ((∑ j, mixedExponent (ab j))
      - ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hexpnp
  have h24 : (3 : ℝ) ^ semigroupR r * (8 : ℝ) ^ semigroupR r
      = (24 : ℝ) ^ semigroupR r := by
    rw [← mul_pow]
    norm_num
  have hNe : (N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24) ^ semigroupR r
      = N ^ ((1 - 12 / Real.sqrt (r : ℝ)) * ((semigroupR r : ℕ) : ℝ))
        / (24 : ℝ) ^ semigroupR r := by
    rw [div_pow, ← Real.rpow_natCast (N ^ (1 - 12 / Real.sqrt (r : ℝ))) (semigroupR r),
      ← Real.rpow_mul hNpos.le]
  have hexp : (1 - 12 / Real.sqrt (r : ℝ)) * ((semigroupR r : ℕ) : ℝ)
      + ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))
      = (∑ j, mixedExponent (ab j))
        - ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ)) := by ring
  have hcombine : N ^ ((1 - 12 / Real.sqrt (r : ℝ)) * ((semigroupR r : ℕ) : ℝ))
      * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))
      = N ^ ((∑ j, mixedExponent (ab j))
        - ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ))) := by
    rw [← Real.rpow_add hNpos, hexp]
  have hfinal : (N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24) ^ semigroupR r
      * ((((r + 1)! : ℕ) : ℝ)
        * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
          * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ)))) ≤ 1 := by
    rw [hNe]
    have hstep : N ^ ((1 - 12 / Real.sqrt (r : ℝ)) * ((semigroupR r : ℕ) : ℝ))
          / (24 : ℝ) ^ semigroupR r
          * ((((r + 1)! : ℕ) : ℝ)
            * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
              * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))))
        = ((((r + 1)! : ℕ) : ℝ)
            * (2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
            * (N ^ ((1 - 12 / Real.sqrt (r : ℝ)) * ((semigroupR r : ℕ) : ℝ))
              * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))))
          / (24 : ℝ) ^ semigroupR r := by ring
    have h24pos : (0 : ℝ) < (24 : ℝ) ^ semigroupR r := by positivity
    rw [hstep, hcombine, div_le_one h24pos]
    calc (((r + 1)! : ℕ) : ℝ)
          * (2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
          * N ^ ((∑ j, mixedExponent (ab j))
            - ((semigroupR r : ℕ) : ℝ) * (12 / Real.sqrt (r : ℝ)))
        ≤ (3 : ℝ) ^ semigroupR r * (8 : ℝ) ^ semigroupR r * 1 :=
          mul_le_mul (mul_le_mul h3bound h2bound (Real.rpow_nonneg (by norm_num) _)
            (by positivity)) hNle1 (Real.rpow_nonneg hNpos.le _) (by positivity)
      _ = (24 : ℝ) ^ semigroupR r := by rw [mul_one, h24]
  by_contra hcon
  push Not at hcon
  have hpowlt : H ^ semigroupR r
      < (N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24) ^ semigroupR r :=
    pow_lt_pow_left₀ hcon hH0 hRpos.ne'
  have hCpos : (0 : ℝ) < (((r + 1)! : ℕ) : ℝ)
      * ((2 : ℝ) ^ (((semigroupR r : ℕ) : ℝ) + 2 * ∑ j, mixedExponent (ab j))
        * N ^ ((∑ j, mixedExponent (ab j)) - ((semigroupR r : ℕ) : ℝ))) := by
    have hc : (0 : ℝ) < (((r + 1)! : ℕ) : ℝ) := by
      have hpos := (r + 1).factorial_pos
      exact_mod_cast hpos
    exact mul_pos hc (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hNpos _))
  have hlt := mul_lt_mul_of_pos_right hpowlt hCpos
  linarith [hmain, hfinal, hlt]

/-! ### Sorting the crude exponent family -/

/-- **Sorted crude semigroup family.**  The injective family of `exists_mixedExponent_family`
can be reindexed so that its mixed exponents are strictly increasing, which is the shape the
generalized Vandermonde determinant requires.  Sorting preserves the pointwise bound and the
total weight; strictness comes from `mixedExponent_injective`, hence from the irrationality
of `θ`. -/
theorem exists_strictMono_mixedExponent_family (r : ℕ) :
    ∃ ab : Fin (r + 1) → ℕ × ℕ, StrictMono (fun j => mixedExponent (ab j)) ∧
      (∀ j, mixedExponent (ab j) ≤ 6 * Real.sqrt (r : ℝ)) ∧
      (∑ j, mixedExponent (ab j)) ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by
  obtain ⟨ab, hinj, hle, hsum⟩ := exists_mixedExponent_family r
  refine ⟨ab ∘ Tuple.sort (fun j => mixedExponent (ab j)), ?_, fun j => hle _, ?_⟩
  · have hmono : Monotone ((fun j => mixedExponent (ab j)) ∘
        Tuple.sort (fun j => mixedExponent (ab j))) :=
      Tuple.monotone_sort (fun j => mixedExponent (ab j))
    have hinj' : Function.Injective ((fun j => mixedExponent (ab j)) ∘
        Tuple.sort (fun j => mixedExponent (ab j))) :=
      (mixedExponent_injective.comp hinj).comp
        (Tuple.sort (fun j => mixedExponent (ab j))).injective
    exact hmono.strictMono_of_injective hinj'
  · calc (∑ j, mixedExponent ((ab ∘ Tuple.sort (fun j => mixedExponent (ab j))) j))
        = ∑ j, mixedExponent (ab j) :=
          Equiv.sum_comp (Tuple.sort (fun j => mixedExponent (ab j)))
            (fun j => mixedExponent (ab j))
      _ ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := hsum

/-! ### Counting candidates in a window and in a dyadic block -/

/-- **Semigroup interval count** (`sg:cor-semigroup-interval-count`).  For `r ≥ 144`, a finite
set `S` of natural candidates inside `[N, N + H]` with `N ≥ 1` satisfies

`#S ≤ r + 24 r H / N ^ (1 - 12 / √r)`,

which is the report's `#(Cand ∩ [N, N+H]) ≤ r + 24 r H N ^ (-1 + 12/√r)`.  The span bound
`explicit_span_lower_bound` is applied to each strictly increasing window of `r + 1` elements
of `S`, with the window's own left endpoint `m 0` in the role of `N`; the
window-span-to-cardinality bridge of `SemigroupWeightBound.lean` then converts spans into a
cardinality bound. -/
theorem card_le_of_semigroup_span (r : ℕ) (hr : 144 ≤ r) (ab : Fin (r + 1) → ℕ × ℕ)
    (hlam : StrictMono fun j => mixedExponent (ab j))
    (hsum : (∑ j, mixedExponent (ab j)) ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ))
    {S : Finset ℕ} {N H : ℝ} (hN : 1 ≤ N) (hH0 : 0 ≤ H)
    (hbound : ∀ x ∈ S, N ≤ (x : ℝ) ∧ (x : ℝ) ≤ N + H)
    (hcand : ∀ x ∈ S, TwoBaseNaturalCandidate x)
    (hfact : ∀ m : Fin (r + 1) → ℕ, StrictMono m → (∀ j, m j ∈ S) →
      NewtonFactorization r m ab ((m 0 : ℕ) : ℝ)) :
    (S.card : ℝ) ≤ (r : ℝ) + 24 * (r : ℝ) * H / N ^ (1 - 12 / Real.sqrt (r : ℝ)) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hs12 : (12 : ℝ) ≤ Real.sqrt (r : ℝ) := twelve_le_sqrt hr
  have hspos : (0 : ℝ) < Real.sqrt (r : ℝ) := lt_of_lt_of_le (by norm_num) hs12
  have he0 : (0 : ℝ) ≤ 1 - 12 / Real.sqrt (r : ℝ) := by
    have h : (12 : ℝ) / Real.sqrt (r : ℝ) ≤ 1 := by
      rw [div_le_one hspos]
      exact hs12
    linarith
  have hLpos : (0 : ℝ) < N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24 :=
    div_pos (Real.rpow_pos_of_pos hNpos _) (by norm_num)
  have hspan : ∀ m : Fin (r + 1) → ℕ, StrictMono m → (∀ j, m j ∈ S) →
      N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24
        ≤ ((m (Fin.last r) : ℕ) : ℝ) - ((m 0 : ℕ) : ℝ) := by
    intro m hmono hmem
    have hm0N : N ≤ ((m 0 : ℕ) : ℝ) := (hbound _ (hmem 0)).1
    have hm0one : (1 : ℝ) ≤ ((m 0 : ℕ) : ℝ) := le_trans hN hm0N
    have hlow' : ∀ i, ((m 0 : ℕ) : ℝ) ≤ ((m i : ℕ) : ℝ) := by
      intro i
      have hmm : m 0 ≤ m i := hmono.monotone (Fin.zero_le i)
      exact_mod_cast hmm
    have hhigh' : ∀ i, ((m i : ℕ) : ℝ)
        ≤ ((m 0 : ℕ) : ℝ) + (((m (Fin.last r) : ℕ) : ℝ) - ((m 0 : ℕ) : ℝ)) := by
      intro i
      have hmm : m i ≤ m (Fin.last r) := hmono.monotone (Fin.le_last i)
      have hc : ((m i : ℕ) : ℝ) ≤ ((m (Fin.last r) : ℕ) : ℝ) := by exact_mod_cast hmm
      linarith
    have hwin := explicit_span_lower_bound r hr m ab hmono
      (fun i => hcand _ (hmem i)) hlam hsum hm0one hlow' hhigh' (hfact m hmono hmem)
    refine le_trans ?_ hwin
    have hbase : N ^ (1 - 12 / Real.sqrt (r : ℝ))
        ≤ ((m 0 : ℕ) : ℝ) ^ (1 - 12 / Real.sqrt (r : ℝ)) :=
      Real.rpow_le_rpow hNpos.le hm0N he0
    linarith
  have hcount := card_le_of_window_span_of_strictMono (r := r) hLpos hH0 hbound hspan
  have heq : (r : ℝ) * H / (N ^ (1 - 12 / Real.sqrt (r : ℝ)) / 24)
      = 24 * (r : ℝ) * H / N ^ (1 - 12 / Real.sqrt (r : ℝ)) := by
    rw [div_div_eq_mul_div]
    ring
  rw [heq] at hcount
  exact hcount

/-- **Explicit `O((log X)^2)` dyadic bound** (`sg:cor-semigroup-log-square`).  Granted the
Newton divided-difference input for every order, any finite set of natural candidates inside
a dyadic block `[X, 2X]` has at most `10000 L ^ 2` elements, for any `L ≥ 1` dominating
`log X`.

The choice `r = ⌈144 L^2⌉` makes `√r ≥ 12 L`, hence
`X ^ (12/√r) = exp(12 log X / √r) ≤ e`, and `card_le_of_semigroup_span` with `N = H = X`
gives `#S ≤ (1 + 24 e) r ≤ (1 + 24 e) · 145 L^2 < 10000 L^2`.

The value of this bound is conceptual independence, not its constant: it comes from
positivity and integrality of generalized Vandermonde determinants, and uses no prime-factor
valuation rank of candidates. -/
theorem card_le_ten_thousand_log_sq
    (hfact : ∀ (r : ℕ) (m : Fin (r + 1) → ℕ) (ab : Fin (r + 1) → ℕ × ℕ),
      StrictMono m → (∀ i, TwoBaseNaturalCandidate (m i)) →
      NewtonFactorization r m ab ((m 0 : ℕ) : ℝ))
    {X : ℝ} (hX : 1 ≤ X) {S : Finset ℕ}
    (hmem : ∀ x ∈ S, TwoBaseNaturalCandidate x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * X)
    {Lg : ℝ} (hLg1 : 1 ≤ Lg) (hlogLg : Real.log X ≤ Lg) :
    (S.card : ℝ) ≤ 10000 * Lg ^ 2 := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hLgpos : (0 : ℝ) < Lg := lt_of_lt_of_le zero_lt_one hLg1
  have hLgsq : (1 : ℝ) ≤ Lg ^ 2 := by nlinarith [hLg1]
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ⌈144 * Lg ^ 2⌉₊ := ⟨_, rfl⟩
  have hrR : (144 : ℝ) * Lg ^ 2 ≤ (r : ℝ) := by
    rw [hrdef]
    exact Nat.le_ceil _
  have hr144 : 144 ≤ r := by
    have h : (144 : ℝ) ≤ (r : ℝ) := by linarith [hrR, hLgsq]
    exact_mod_cast h
  have hrlt : (r : ℝ) < 144 * Lg ^ 2 + 1 := by
    rw [hrdef]
    exact Nat.ceil_lt_add_one (by positivity)
  have hrle : (r : ℝ) ≤ 145 * Lg ^ 2 := by linarith [hrlt, hLgsq]
  have hsqrt : 12 * Lg ≤ Real.sqrt (r : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (12 * Lg) ^ 2 = 144 * Lg ^ 2 := by ring
      _ ≤ (r : ℝ) := hrR
  have hspos : (0 : ℝ) < Real.sqrt (r : ℝ) :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 12 * Lg) hsqrt
  obtain ⟨ab, hlam, _hle, hsum⟩ := exists_strictMono_mixedExponent_family r
  have hbound : ∀ x ∈ S, X ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) ≤ X + X := by
    intro x hx
    obtain ⟨_, h1, h2⟩ := hmem x hx
    exact ⟨h1, by linarith⟩
  have hcount := card_le_of_semigroup_span r hr144 ab hlam hsum hX hXpos.le hbound
    (fun x hx => (hmem x hx).1)
    (fun m hmono hmm => hfact r m ab hmono fun i => (hmem _ (hmm i)).1)
  have hXne : X ^ (1 - 12 / Real.sqrt (r : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hXpos _).ne'
  have hratio : X ^ (12 / Real.sqrt (r : ℝ)) * X ^ (1 - 12 / Real.sqrt (r : ℝ)) = X := by
    rw [← Real.rpow_add hXpos,
      show (12 / Real.sqrt (r : ℝ)) + (1 - 12 / Real.sqrt (r : ℝ)) = 1 by ring,
      Real.rpow_one]
  have hdiv : 24 * (r : ℝ) * X / X ^ (1 - 12 / Real.sqrt (r : ℝ))
      = 24 * (r : ℝ) * X ^ (12 / Real.sqrt (r : ℝ)) := by
    rw [eq_comm, eq_div_iff hXne]
    calc 24 * (r : ℝ) * X ^ (12 / Real.sqrt (r : ℝ))
          * X ^ (1 - 12 / Real.sqrt (r : ℝ))
        = 24 * (r : ℝ) * (X ^ (12 / Real.sqrt (r : ℝ))
            * X ^ (1 - 12 / Real.sqrt (r : ℝ))) := by ring
      _ = 24 * (r : ℝ) * X := by rw [hratio]
  rw [hdiv] at hcount
  have hexpb : X ^ (12 / Real.sqrt (r : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXpos]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (12 : ℝ) / Real.sqrt (r : ℝ) ≤ 1 / Lg := by
      rw [div_le_div_iff₀ hspos hLgpos]
      linarith [hsqrt]
    have h2 : Real.log X * (12 / Real.sqrt (r : ℝ)) ≤ Lg * (1 / Lg) :=
      mul_le_mul hlogLg h1 (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
    rwa [mul_one_div, div_self hLgpos.ne'] at h2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hstep : 24 * (r : ℝ) * X ^ (12 / Real.sqrt (r : ℝ))
      ≤ 24 * (r : ℝ) * 2.7182818286 :=
    mul_le_mul_of_nonneg_left (le_trans hexpb he.le) (by positivity)
  calc (S.card : ℝ) ≤ (r : ℝ) * (1 + 24 * 2.7182818286) := by linarith [hcount, hstep]
    _ ≤ (145 * Lg ^ 2) * (1 + 24 * 2.7182818286) :=
        mul_le_mul_of_nonneg_right hrle (by norm_num)
    _ ≤ 10000 * Lg ^ 2 := by nlinarith [sq_nonneg Lg]

/-- The report's statement of `sg:cor-semigroup-log-square`, with the explicit weight
`L = max(1, log X)`. -/
theorem card_le_ten_thousand_max_log_sq
    (hfact : ∀ (r : ℕ) (m : Fin (r + 1) → ℕ) (ab : Fin (r + 1) → ℕ × ℕ),
      StrictMono m → (∀ i, TwoBaseNaturalCandidate (m i)) →
      NewtonFactorization r m ab ((m 0 : ℕ) : ℝ))
    {X : ℝ} (hX : 1 ≤ X) {S : Finset ℕ}
    (hmem : ∀ x ∈ S, TwoBaseNaturalCandidate x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * X) :
    (S.card : ℝ) ≤ 10000 * (max 1 (Real.log X)) ^ 2 :=
  card_le_ten_thousand_log_sq hfact hX hmem (le_max_left _ _) (le_max_right _ _)

end

end LeanProofs.TwoBaseIntegerExponent
