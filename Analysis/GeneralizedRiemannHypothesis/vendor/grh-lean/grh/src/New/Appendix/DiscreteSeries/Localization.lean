import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
import New.Appendix.DiscreteSeries.SteepParameters

/-!
# Localizing products of discrete series coefficients near the compact subgroups

This file treats a group `S` with a map `j : S →* U(ε) × U(η)` that satisfies
`New.DiscreteSeries.IsLaplaceDatum`. It proves facts about `New.HCParam.laplaceIntegrand`, the
product of the first discrete series coefficient, the conjugate of the second and `exp (-φ)`. It
shows that a coefficient with a large gap decays away from the maximal compact subgroup. It also
shows that, if `1 ≤ B` and both noncompact parts at `s` are small, the integrand takes the same
value at some `t` for which both components of `j t` are near `1`.

## Main definitions and results

* `New.DiscreteSeries.noncompactPart ε g`: the noncompact part `g - blockDiagPart ε g` of a
  matrix `g`.
* A coefficient with a large gap is small where the noncompact part of its argument is large
  (`New.DiscreteSeries.norm_dsCoeff_pow_four_le`).
* If `1 ≤ B` and both noncompact parts at `s` are small, then `laplaceIntegrand` takes the same
  value at some `t` for which both components of `j t` are near `1`
  (`New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le`).

Notions from other files:
* `New.USign ε`: the unitary group `U(ε)` of the diagonal matrix `signMatrix ε` of the signs `ε`.
* `New.blockDiagPart ε g`: the compact part of `g`, which keeps the entries `g i j` with
  `ε i = ε j`.
* `New.HCParam.lowestKType l`, `New.HCParam.dsCoeff l`: the highest weight of the lowest `K`-type
  of the parameter `l`, and the matrix coefficient of that `K`-type.
* `New.DiscreteSeries.IsLaplaceDatum`: the properties of `j` and `φ` that Laplace's method uses.
* `New.HCParam.laplaceIntegrand`: the function to which Laplace's method applies.

## Relation to the literature

This file uses the discrete series coefficient that is known as Flensted-Jensen's function, the
coefficient of the lowest `K`-type of a discrete series
(defined in `Lib.DiscreteSeries.FlenstedJensen.Defs`).
-/

noncomputable section

section Localization

open Finset Matrix Complex ComplexConjugate Set ComplexOrder Int New.HCParam

namespace New.DiscreteSeries

open Norms.Frobenius

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] {ε : n → ℤˣ} {l : HCParam ε} {η : m → ℤˣ} {k : HCParam η}
  {j : S →* USign ε × USign η} {τ : X → m} {B : ℝ} {M : ℕ}

/-! ### The relation `g ε gᴴ = ε` row by row -/

variable (ε) in
/-- The noncompact part `A - blockDiagPart ε A` of a matrix `A` for the signs `ε`: it keeps the
entries `A i j` with `ε i ≠ ε j` and puts zero elsewhere. -/
def noncompactPart (A : Matrix n n ℂ) : Matrix n n ℂ := A - blockDiagPart ε A

/-- Let `ε : n → ℤˣ` be a vector of signs and let `g` be in `U(ε) = USign ε`, the unitary group of
the diagonal matrix of `ε`. The entry `(i, i)` of the relation `g ε gᴴ = ε` reads
`2 re (x i i) = 2 ∑ j, ‖y i j‖² - ∑ j, ‖x i j‖²`, where `x = g - 1` and `y = noncompactPart ε g`
keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma two_mul_re_sub_one_apply (g : USign ε) (i : n) :
    2 * (((g : Matrix n n ℂ) - 1) i i).re =
      2 * ∑ j : n, ‖noncompactPart ε g i j‖ ^ 2 - ∑ j : n, ‖((g : Matrix n n ℂ) - 1) i j‖ ^ 2 := by
  have h_form : (g : Matrix n n ℂ) * (signMatrix ε * (g : Matrix n n ℂ)ᴴ * signMatrix ε) = 1 := by
    rw [← U.inv_coe_eq_mul_conjTranspose_mul, mul_nonsing_inv _ g.1.det_ne_zero.isUnit]
  generalize (g : Matrix n n ℂ) = A at h_form ⊢
  have h_signed : ∑ j : n, (‖A i j‖ ^ 2 - 2 * ‖noncompactPart ε A i j‖ ^ 2) = 1 := by
    have h_entry : (A * (signMatrix ε * Aᴴ * signMatrix ε)) i i = 1 := by simp [h_form]
    rw [← ofReal_inj, ofReal_one, ← h_entry, Matrix.mul_apply, ofReal_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rcases units_eq_one_or (ε i) with hi | hi <;> rcases units_eq_one_or (ε j) with hj | hj <;>
      simp [signMatrix, noncompactPart, blockDiagPart, hi, hj, mul_conj', two_mul]
  have h_shift (j : n) :
      ‖(A - 1) i j‖ ^ 2 = ‖A i j‖ ^ 2 + if i = j then 1 - 2 * (A i i).re else 0 := by
    rcases eq_or_ne i j with rfl | hij
    · simp [Complex.sq_norm, normSq_apply]
      ring
    · simp [hij]
  simp only [sum_sub_distrib, ← mul_sum] at h_signed
  rw [sum_congr rfl fun j _ ↦ h_shift j]
  simp [sum_add_distrib]
  linarith

/-- Let `g` be in `U(ε) = USign ε`, the unitary group of the diagonal matrix of the signs
`ε : n → ℤˣ`. Let `v`, `w` be integer vectors with `a (v i)² ≤ w i` for all `i` and `w i ≤ C` at
each index whose sign differs from that of some other index. Then, in Frobenius norms,
`a ‖v (g - 1)‖² + 2 re tr (w (g - 1)) ≤ 2 C ‖y‖²`. Here `v` and `w` act as the diagonal matrices
`intDiagonal v` and `intDiagonal w`, and `y = noncompactPart ε g` keeps the entries `g i j` with
`ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_sq_add_re_trace_le (g : USign ε) (a C : ℝ) (v w : n → ℤ)
    (h_lower : ∀ i : n, a * v i ^ 2 ≤ w i) (h_upper : ∀ i j : n, ε i ≠ ε j → w i ≤ C) :
    a * ‖intDiagonal v * ((g : Matrix n n ℂ) - 1)‖ ^ 2 +
        2 * (intDiagonal w * ((g : Matrix n n ℂ) - 1)).trace.re ≤
      2 * C * ‖noncompactPart ε g‖ ^ 2 := by
  -- Multiply the relation `two_mul_re_sub_one_apply` in the row `i` by `w i` and sum over `i`.
  set x : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set y : Matrix n n ℂ := noncompactPart ε g with hy
  have h_row (i : n) : 2 * (x i i).re = 2 * ∑ j : n, ‖y i j‖ ^ 2 - ∑ j : n, ‖x i j‖ ^ 2 :=
    two_mul_re_sub_one_apply g i
  have h_trace : 2 * (intDiagonal w * x).trace.re =
      ∑ i : n, w i * (2 * ∑ j : n, ‖y i j‖ ^ 2 - ∑ j : n, ‖x i j‖ ^ 2) := by
    simp only [← h_row]
    simp [trace, re_sum, mul_sum, mul_left_comm]
  have h_norm : ‖intDiagonal v * x‖ ^ 2 = ∑ i : n, v i ^ 2 * ∑ j : n, ‖x i j‖ ^ 2 := by
    simp [frobenius_norm_sq_eq_sum, diagonal_mul, mul_pow, sq_abs, mul_sum]
  have h_noncompact (i : n) : w i * ∑ j : n, ‖y i j‖ ^ 2 ≤ C * ∑ j : n, ‖y i j‖ ^ 2 := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ ↦ ?_
    rcases eq_or_ne (ε i) (ε j) with hij | hij
    · simp [hy, noncompactPart, blockDiagPart, hij]
    · exact mul_le_mul_of_nonneg_right (h_upper i j hij) (sq_nonneg _)
  rw [h_trace, h_norm, frobenius_norm_sq_eq_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ ?_
  have h_weight : a * v i ^ 2 * ∑ j : n, ‖x i j‖ ^ 2 ≤ w i * ∑ j : n, ‖x i j‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (h_lower i) (by positivity)
  linarith [h_noncompact i]

/-- Let `g` be in `U(ε) = USign ε`, the unitary group of the diagonal matrix of the signs
`ε : n → ℤˣ`. Then `‖g - 1‖² = 2 ‖y‖² - 2 re tr (g - 1)` in Frobenius norms, where
`y = noncompactPart ε g` keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_sub_one_sq (g : USign ε) :
    ‖(g : Matrix n n ℂ) - 1‖ ^ 2 =
      2 * ‖noncompactPart ε g‖ ^ 2 - 2 * ((g : Matrix n n ℂ) - 1).trace.re := by
  set x : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set y : Matrix n n ℂ := noncompactPart ε g
  have h_row (i : n) : ∑ j : n, ‖x i j‖ ^ 2 = 2 * ∑ j : n, ‖y i j‖ ^ 2 - 2 * (x i i).re := by
    linarith [two_mul_re_sub_one_apply g i]
  calc ‖x‖ ^ 2 = ∑ i : n, ∑ j : n, ‖x i j‖ ^ 2 := frobenius_norm_sq_eq_sum
    _ = ∑ i : n, (2 * ∑ j : n, ‖y i j‖ ^ 2 - 2 * (x i i).re) := sum_congr rfl fun i _ ↦ h_row i
    _ = 2 * ‖y‖ ^ 2 - 2 * x.trace.re := by
      simp [frobenius_norm_sq_eq_sum, trace, re_sum, mul_sum, sum_sub_distrib]

omit [Fintype n] in
lemma conjTranspose_signMatrix : (signMatrix ε)ᴴ = signMatrix ε := by simp [signMatrix]

lemma norm_signMatrix_mul (A : Matrix n n ℂ) : ‖signMatrix ε * A‖ = ‖A‖ :=
  frobenius_norm_mul_of_unitary (by rw [conjTranspose_signMatrix, signMatrix_mul_self]) A

lemma norm_signMatrix_mul_conjTranspose_mul_signMatrix (A : Matrix n n ℂ) :
    ‖signMatrix ε * Aᴴ * signMatrix ε‖ = ‖A‖ := by
  rw [mul_assoc, norm_signMatrix_mul, ← conjTranspose_signMatrix (ε := ε), ← conjTranspose_mul,
    frobenius_norm_conjTranspose, norm_signMatrix_mul]

/-- For `g` in `U(ε)`, the noncompact parts of `g⁻¹` and of `g` have the same Frobenius norm. -/
lemma norm_noncompactPart_inv (g : USign ε) :
    ‖noncompactPart ε (g⁻¹ : USign ε)‖ = ‖noncompactPart ε g‖ := by
  have h_inv : noncompactPart ε (g⁻¹ : USign ε) =
      signMatrix ε * (noncompactPart ε g)ᴴ * signMatrix ε := by
    rw [U.coe_inv (signMatrix_mul_self ε) g]
    ext i j
    by_cases hij : ε i = ε j <;> simp [signMatrix, noncompactPart, blockDiagPart, hij, Ne.symm]
  rw [h_inv, norm_signMatrix_mul_conjTranspose_mul_signMatrix]

/-! ### The block on `X` -/

/-- A positive semidefinite matrix `z` is at least as close to `1` as `z²`, in Frobenius norm. -/
lemma norm_sub_one_le_norm_mul_self_sub_one {z : Matrix X X ℂ} (hz : z.PosSemidef) :
    ‖z - 1‖ ≤ ‖z * z - 1‖ := by
  -- As `z² - 1 = (z + 1) (z - 1)` and `(z + 1)² - 1 = z² + 2 z ≥ 0`, the difference of the squares
  -- is the trace of a positive semidefinite matrix.
  have h_pos : ((z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1)).PosSemidef :=
    ((posSemidef_conjTranspose_mul_self z).add (hz.add hz)).conjTranspose_mul_mul_same _
  have h_diff : (z - 1)ᴴ * (zᴴ * z + (z + z)) * (z - 1) =
      (z * z - 1)ᴴ * (z * z - 1) - (z - 1)ᴴ * (z - 1) := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_one, hz.isHermitian.eq]
    noncomm_ring
  have h_trace : (0 : ℂ) ≤ (‖z * z - 1‖ ^ 2 : ℝ) - (‖z - 1‖ ^ 2 : ℝ) := by
    rw [← trace_star_mul_self_eq_norm_sq, ← trace_star_mul_self_eq_norm_sq, ← trace_sub, ← h_diff]
    exact h_pos.trace_nonneg
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (real_le_real.1 (sub_nonneg.1 h_trace))

/-- The indicator function of the coordinates off `X`: under `e : X ⊕ Fin M ≃ n` it is `0` on the
image of `X` and `1` on the image of `Fin M`. -/
def offBlockIndicator (e : X ⊕ Fin M ≃ n) (i : n) : ℤ := (e.symm i).elim 0 1

/-- The block of a matrix with rows and columns in `X`, seen in `n` through `e : X ⊕ Fin M ≃ n`. -/
abbrev onBlock (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) : Matrix X X ℂ :=
  A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)

lemma norm_onBlock_le (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) : ‖onBlock e A‖ ≤ ‖A‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [frobenius_norm_sq_eq_sum, ← e.sum_comp, sum_add_distrib, add_assoc]
  positivity

/-- The square of the Frobenius norm of `A` is at most the sum of those of its rows off `X`, its
columns off `X` and its block `onBlock e A` on `X`, with `X` seen in `n` through `e`. Multiplication
by `intDiagonal (offBlockIndicator e)` on the left (right) keeps the rows (columns) off `X`. -/
lemma norm_sq_le_rows_add_columns_add_block (e : X ⊕ Fin M ≃ n) (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤
      ‖intDiagonal (offBlockIndicator e) * A‖ ^ 2 + ‖A * intDiagonal (offBlockIndicator e)‖ ^ 2 +
        ‖onBlock e A‖ ^ 2 := by
  -- Only the entries in both a row and a column off `X` are counted twice on the right.
  have h_count :
      ‖intDiagonal (offBlockIndicator e) * A‖ ^ 2 + ‖A * intDiagonal (offBlockIndicator e)‖ ^ 2 +
          ‖onBlock e A‖ ^ 2 =
        ‖A‖ ^ 2 + ∑ a : Fin M, ∑ b : Fin M, ‖A (e (.inr a)) (e (.inr b))‖ ^ 2 := by
    simp [frobenius_norm_sq_eq_sum, ← e.sum_comp, offBlockIndicator, sum_add_distrib]
    ring
  rw [h_count, le_add_iff_nonneg_right]
  positivity

/-- Let `g` be in `U(ε)`, the signs being `+1` on `X`, and let `a = onBlock e g` be the block of `g`
on `X`. Then `‖aᴴ a - 1‖` is at most the square of the norm of the rows of `g - 1` off `X`, which
left multiplication by the diagonal matrix `intDiagonal (offBlockIndicator e)` keeps. -/
lemma norm_onBlock_gram_sub_one_le (e : X ⊕ Fin M ≃ n) (hε : ∀ x : X, ε (e (.inl x)) = 1)
    (g : USign ε) :
    ‖(onBlock e g)ᴴ * onBlock e g - 1‖ ≤
      ‖intDiagonal (offBlockIndicator e) * ((g : Matrix n n ℂ) - 1)‖ ^ 2 := by
  -- The block on `X` of `gᴴ ε g = ε` reads `aᴴ a + onBlock e (Wᴴ ε W) = 1`, where `W` consists of
  -- the rows of `g - 1` off `X`.
  have h_form : (g : Matrix n n ℂ)ᴴ * signMatrix ε * (g : Matrix n n ℂ) = signMatrix ε :=
    mem_U.1 g.2
  generalize (g : Matrix n n ℂ) = A at h_form ⊢
  set W : Matrix n n ℂ := intDiagonal (offBlockIndicator e) * (A - 1) with hW
  have hW_on (x : X) (i : n) : W (e (.inl x)) i = 0 := by simp [hW, offBlockIndicator]
  have hW_off (a : Fin M) (x : X) : W (e (.inr a)) (e (.inl x)) = A (e (.inr a)) (e (.inl x)) := by
    simp [hW, offBlockIndicator]
  have h_split : onBlock e (Aᴴ * signMatrix ε * A) =
      (onBlock e A)ᴴ * onBlock e A + onBlock e (Wᴴ * signMatrix ε * W) := by
    ext x y
    simp [Matrix.mul_apply, signMatrix, diagonal_apply, ← e.sum_comp, hε, hW_on, hW_off]
  have h_one : onBlock e (signMatrix ε) = 1 := by
    ext
    simp [signMatrix, hε, one_apply, diagonal_apply]
  rw [h_form, h_one] at h_split
  calc ‖(onBlock e A)ᴴ * onBlock e A - 1‖ = ‖onBlock e (Wᴴ * (signMatrix ε * W))‖ := by
        rw [h_split, sub_add_cancel_left, norm_neg, mul_assoc]
    _ ≤ ‖Wᴴ‖ * ‖signMatrix ε * W‖ := (norm_onBlock_le e _).trans (norm_mul_le _ _)
    _ = ‖W‖ ^ 2 := by rw [frobenius_norm_conjTranspose, norm_signMatrix_mul, sq]

/-- If `u` is unitary (`uᴴ * u = 1`) and `f : X ⊕ Y ≃ n` sends `X` to coordinates where `ε` is `1`,
then `u`, extended by `1` on the coordinates from `Y`, is an element `s` of `USign ε`: `s -
1 = inclMatrix ℂ (f ∘ .inl) * (u - 1) * (inclMatrix ℂ (f ∘ .inl))ᴴ`. Here `inclMatrix ℂ (f ∘ .inl)`
is the matrix of the inclusion of `X` in `n`. -/
lemma exists_unitary_sub_one_eq_inclMatrix {u : Matrix X X ℂ} {Y : Type} [Fintype Y]
    (f : X ⊕ Y ≃ n) (hε : ∀ x : X, ε (f (.inl x)) = 1) (hu : uᴴ * u = 1) :
    ∃ s : USign ε, (s : Matrix n n ℂ) - 1 =
      inclMatrix ℂ (f ∘ .inl) * (u - 1) * (inclMatrix ℂ (f ∘ .inl))ᴴ := by
  set Q : Matrix n X ℂ := inclMatrix ℂ (f ∘ .inl) with hQ
  have hQ_iso : Qᴴ * Q = 1 := by ext; simp [hQ, inclMatrix, Matrix.mul_apply, one_apply, eq_comm]
  have hQ_sgn : signMatrix ε * Q = Q := by
    ext i x
    by_cases hi : i = f (.inl x) <;> simp [hQ, inclMatrix, signMatrix, one_apply, hε, hi]
  have hQ_sgn' : Qᴴ * signMatrix ε = Qᴴ := by
    rw [← conjTranspose_signMatrix, ← conjTranspose_mul, hQ_sgn]
  have h_expand : (uᴴ - 1) + (u - 1) + (uᴴ - 1) * (u - 1) = uᴴ * u - 1 := by noncomm_ring
  suffices h_form : (1 + Q * (u - 1) * Qᴴ)ᴴ * signMatrix ε * (1 + Q * (u - 1) * Qᴴ) =
      signMatrix ε from
    ⟨U.of IsHermitianInvolution.isUnit _ h_form, by simp⟩
  calc (1 + Q * (u - 1) * Qᴴ)ᴴ * signMatrix ε * (1 + Q * (u - 1) * Qᴴ)
      = signMatrix ε + Q * (uᴴ - 1) * (Qᴴ * signMatrix ε) + signMatrix ε * Q * (u - 1) * Qᴴ +
          Q * (uᴴ - 1) * (Qᴴ * (signMatrix ε * Q)) * (u - 1) * Qᴴ := by
        simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc, add_left_comm]
    _ = signMatrix ε + Q * ((uᴴ - 1) + (u - 1) + (uᴴ - 1) * (u - 1)) * Qᴴ := by
        simp [hQ_sgn, hQ_sgn', hQ_iso, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
    _ = signMatrix ε := by simp [h_expand, hu]

variable {e : X ⊕ Fin M ≃ n} {φ : S → ℂ}

/-! ### The phases at the logarithms -/

/-- For `‖A‖ ≤ 1 / 2` (Frobenius norm) and `0 ≤ r ≤ 1`, the geometric series of `(1 + r • A)⁻¹` may
be multiplied by `D` and `A` and traced term by term. -/
lemma hasSum_trace_geom {A : Matrix n n ℂ} (hA : ‖A‖ ≤ 2⁻¹) (D : Matrix n n ℂ) {r : ℝ}
    (hr : r ∈ Set.Icc 0 1) :
    HasSum (fun i : ℕ ↦ trace (D * ((-(r • A)) ^ i * A))) (trace (D * ((1 + r • A)⁻¹ * A))) := by
  have h_small : ‖-(r • A)‖ < 1 := by
    simpa using (norm_smul_le_of_le_one r hA hr).trans_lt two_inv_lt_one
  have h_geom : HasSum (fun i : ℕ ↦ D * ((-(r • A)) ^ i * A))
      (D * (Ring.inverse (1 - -(r • A)) * A)) :=
    ((hasSum_geom_series_inverse _ h_small).mul_right A).mul_left D
  simpa [← nonsing_inv_eq_ringInverse] using
    h_geom.mapL (traceLinearMap n ℂ ℂ).toContinuousLinearMap

/-- The difference `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')` of the two phases, for the weights
`μ`, `μ'` of the lowest `K`-types of `l` and `k`, is compatible with subtraction of pairs. -/
lemma phase_sub (y z : Matrix n n ℂ × Matrix m m ℂ) :
    l.phase k (y - z) = l.phase k y - l.phase k z := by
  simp [phase, mul_sub, sub_sub_sub_comm]

/-- For a pair of matrices put `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')`, where `μ` and `μ'` are
the diagonal matrices of the weights of the lowest `K`-types of the parameters `l` and `k`. Let
`j : S →* U(ε) × U(η)` and `φ : S → ℂ` satisfy `IsLaplaceDatum`, of which two conditions are used:
`φ` is additive, and `l.phase k (g - 1, g' - 1) = φ s` for `(g, g') = j s`. Then
`l.phase k ((g - 1) ^ (i + 1), (g' - 1) ^ (i + 1))` is `φ s` for `i = 0` and `0` for `i > 0`. -/
lemma IsLaplaceDatum.phase_pow_mul (hj : IsLaplaceDatum l k j τ B e φ) (s : S) (i : ℕ) :
    l.phase k (subOnePair j s ^ i * subOnePair j s) = 0 ^ i * φ s := by
  set x : Matrix n n ℂ × Matrix m m ℂ := subOnePair j s with hx
  -- For the induction, insert the factor `j t = 1 + subOnePair j t`; then put `t = 1`.
  suffices h_powers : ∀ t : S, l.phase k (x ^ i * x * (1 + subOnePair j t)) = 0 ^ i * φ s by
    rw [← h_powers 1, show subOnePair j 1 = 0 by simp, add_zero, mul_one]
  have h_step (t : S) : x * (1 + subOnePair j t) = subOnePair j (s * t) - subOnePair j t := by
    ext1 <;> simp [hx, sub_mul]
  intro t
  induction i generalizing t with
  | zero =>
    rw [pow_zero, one_mul, h_step, phase_sub, hj.phase_eq, hj.phase_eq, hj.phase_mul]
    ring
  | succ i ih =>
    have h_split : x ^ (i + 1) * x * (1 + subOnePair j t) =
        x ^ i * x * (1 + subOnePair j (s * t)) - x ^ i * x * (1 + subOnePair j t) := by
      rw [← mul_sub, add_sub_add_left_eq_sub, ← h_step, pow_succ, mul_assoc]
    rw [h_split, phase_sub, ih, ih]
    ring

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`. For a pair of matrices
put `l.phase k (Y, Y') = tr (μ Y) - tr (μ' Y')`, where `μ` and `μ'` are the diagonal matrices of the
weights of the lowest `K`-types of `l` and `k`. Let `j : S →* U(ε) × U(η)` and `φ : S → ℂ` satisfy
`IsLaplaceDatum`. In particular the function `φ` is additive, and `l.phase k (g - 1, g' - 1) = φ s`
for `(g, g') = j s`, where `(g - 1, g' - 1) = subOnePair j s`. If `g - 1` and `g' - 1` have
Frobenius norm at most `1 / 2`, then `l.phase k (log g, log g')` is again `φ s`. Here
`log g = logOneAdd (g - 1)`, and `logOneAdd Y` is the logarithm of `1 + Y`. -/
lemma IsLaplaceDatum.phase_logOneAdd (hj : IsLaplaceDatum l k j τ B e φ) (s : S)
    (h_fst : ‖(subOnePair j s).1‖ ≤ 2⁻¹) (h_snd : ‖(subOnePair j s).2‖ ≤ 2⁻¹) :
    l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s := by
  -- In the geometric series of `phase ((1 + r • x)⁻¹ * x)` only the term `phase x = φ s` is left,
  -- by `phase_pow_mul`; integrate over `r`.
  have h_powers (i : ℕ) : l.phase k (subOnePair j s ^ i * subOnePair j s) = 0 ^ i * φ s :=
    hj.phase_pow_mul s i
  set x : Matrix n n ℂ × Matrix m m ℂ := subOnePair j s
  let D : Matrix n n ℂ := intDiagonal l.lowestKType
  let D' : Matrix m m ℂ := intDiagonal k.lowestKType
  have h_integrand (r : ℝ) (hr : r ∈ Set.Icc 0 1) :
      (D * ((1 + r • x.1)⁻¹ * x.1)).trace - (D' * ((1 + r • x.2)⁻¹ * x.2)).trace = φ s := by
    have h_term (i : ℕ) :
        (D * ((-(r • x.1)) ^ i * x.1)).trace - (D' * ((-(r • x.2)) ^ i * x.2)).trace =
          (-r : ℂ) ^ i * (0 ^ i * φ s) := by
      rw [← h_powers]
      simp [D, D', phase, ← neg_smul, smul_pow, mul_sub]
    have h_single : HasSum (fun i : ℕ ↦ (-r : ℂ) ^ i * (0 ^ i * φ s)) (φ s) := by
      convert hasSum_ite_eq (0 : ℕ) (φ s) with i
      cases i <;> simp
    refine ((hasSum_trace_geom h_fst D hr).sub (hasSum_trace_geom h_snd D' hr)).unique ?_
    simpa only [h_term] using h_single
  calc l.phase k (x.map logOneAdd logOneAdd)
      = ∫ r : ℝ in 0..1,
          ((D * ((1 + r • x.1)⁻¹ * x.1)).trace - (D' * ((1 + r • x.2)⁻¹ * x.2)).trace) := by
        rw [intervalIntegral.integral_sub
            (intervalIntegrable_trace_mul_inv_one_add_smul_mul h_fst D)
            (intervalIntegrable_trace_mul_inv_one_add_smul_mul h_snd D'),
          integral_trace_mul_inv_one_add_smul_mul h_fst,
          integral_trace_mul_inv_one_add_smul_mul h_snd, phase, Prod.map_fst, Prod.map_snd]
    _ = ∫ _ : ℝ in 0..1, φ s :=
        intervalIntegral.integral_congr fun r hr ↦
          h_integrand r (by rwa [Set.uIcc_of_le zero_le_one] at hr)
    _ = φ s := by simp

/-! ### Left translation by `U(X)` -/

/-- If `x - 1` vanishes in the rows `i` with `w i ≠ 0`, then the principal minor of `x` on
`{i | c ≤ w i}` is `det x` for `c ≤ 0` and `1` for `c > 0`. -/
lemma principalMinor_eq_ite_det {w : n → ℤ} {x : Matrix n n ℂ}
    (hx : ∀ i j : n, w i ≠ 0 → (x - 1) i j = 0) (c : ℤ) :
    principalMinor x (fun i : n ↦ c ≤ w i) = if c ≤ 0 then x.det else 1 := by
  have h_cut : diagonal (fun i : n ↦ if c ≤ w i then 1 else 0) * (x - 1) =
      if c ≤ 0 then x - 1 else 0 := by
    ext i j
    by_cases hi : w i = 0
    · split_ifs with hc <;> simp [diagonal_mul, hi, hc]
    · split_ifs <;> simp [diagonal_mul, hx i j hi]
  rw [principalMinor_eq_det, ← neg_sub x, mul_neg, h_cut, sub_neg_eq_add]
  split_ifs <;> simp

/-- Let `x` be invertible, with `x i j = 0` for `w i ≠ w j` and with `x - 1` vanishing in the rows
`i` with `w i ≠ 0`. Then left multiplication by `x` preserves `weightMinors w`, the coefficient of
a highest vector of weight `w`. -/
lemma weightMinors_mul_eq_of_zero_weight_block {w : n → ℤ} {x : Matrix n n ℂ} (hx_det : x.det ≠ 0)
    (hx_block : ∀ i j : n, w i ≠ w j → x i j = 0) (hx_row : ∀ i j : n, w i ≠ 0 → (x - 1) i j = 0)
    (y : Matrix n n ℂ) : weightMinors w (x * y) = weightMinors w y := by
  refine finprod_congr fun c ↦ ?_
  have h_mul : principalMinor (x * y) (fun i : n ↦ c ≤ w i) =
      principalMinor x (fun i : n ↦ c ≤ w i) * principalMinor y (fun i : n ↦ c ≤ w i) :=
    principalMinor_mul fun i j _ hi hj _ ↦ .inl (hx_block i j (by omega))
  rw [h_mul, principalMinor_eq_ite_det hx_row]
  split_ifs
  · rw [det_mul, mul_div_mul_left _ _ hx_det]
  · rw [one_mul]

omit [Fintype n] [DecidableEq X] in
/-- A matrix `u` on `X`, placed by `inclMatrix` in the rows and columns in the image of `σ`,
vanishes in the other rows and in the other columns. -/
lemma inclMatrix_mul_mul_conjTranspose_apply_eq_zero {σ : X → n} (u : Matrix X X ℂ) {i j : n}
    (hij : i ∉ range σ ∨ j ∉ range σ) : (inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) i j = 0 := by
  simp only [Set.mem_range, not_exists] at hij
  rcases hij with hi | hj
  · simp [inclMatrix, Matrix.mul_apply, one_apply, fun x ↦ Ne.symm (hi x)]
  · simp [inclMatrix, Matrix.mul_apply, one_apply, hj]

omit [Fintype n] [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`. If a function `f` is constant on the image of `σ`, then `A i j = 0` for `f i ≠ f j`. -/
lemma apply_eq_zero_of_sub_one_eq_inclMatrix {α : Type*} {f : n → α} {c : α} {σ : X → n}
    (hσ : ∀ x : X, f (σ x) = c) {u : Matrix X X ℂ} {A : Matrix n n ℂ}
    (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) {i j : n} (hij : f i ≠ f j) :
    A i j = 0 := by
  have h_outside : i ∉ range σ ∨ j ∉ range σ := by grind
  calc A i j = (A - 1) i j := by simp [show i ≠ j by grind]
    _ = 0 := by rw [hA, inclMatrix_mul_mul_conjTranspose_apply_eq_zero u h_outside]

omit [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the sign is `+1`. Then `A` is block diagonal for the signs `ε`. -/
lemma mem_blockDiagAlg_of_sub_one_eq_inclMatrix {σ : X → n} (hσ_sign : ∀ x : X, ε (σ x) = 1)
    {u : Matrix X X ℂ} {A : Matrix n n ℂ} (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) :
    A ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.2 fun _ _ hij ↦ apply_eq_zero_of_sub_one_eq_inclMatrix hσ_sign hA hij

omit [Fintype n] [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the weight `w` is `0`. Then `A - 1` vanishes in the rows `i` with `w i ≠ 0`. -/
lemma sub_one_apply_eq_zero_of_weight_ne_zero {w : n → ℤ} {σ : X → n}
    (hσ_weight : ∀ x : X, w (σ x) = 0) {u : Matrix X X ℂ} {A : Matrix n n ℂ}
    (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) (i j : n) (hi : w i ≠ 0) :
    (A - 1) i j = 0 := by
  have h_outside : i ∉ range σ := by grind
  rw [hA, inclMatrix_mul_mul_conjTranspose_apply_eq_zero u (.inl h_outside)]

omit [DecidableEq X] in
/-- Let `A - 1` be a matrix `u` on `X` placed, by `inclMatrix`, in the rows and columns in the image
of `σ`, where the weight `w` is `0`. Then the diagonal matrix of `w` kills `A - 1`. -/
lemma intDiagonal_mul_sub_one_eq_zero {w : n → ℤ} {σ : X → n} (hσ_weight : ∀ x : X, w (σ x) = 0)
    {u : Matrix X X ℂ} {A : Matrix n n ℂ} (hA : A - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) :
    intDiagonal w * (A - 1) = 0 := by
  ext i j
  by_cases hi : w i = 0
  · simp [diagonal_mul, hi]
  · simp [diagonal_mul, sub_one_apply_eq_zero_of_weight_ne_zero hσ_weight hA i j hi]

omit [DecidableEq X] in
/-- Let `g₀ ∈ U(ε)` be such that `g₀ - 1` is a matrix `x` on `X` placed, by `inclMatrix`, in the
rows and columns in the image of `σ : X → n`, where the sign is `+1` and the weight `l.lowestKType`
of the lowest `K`-type of the parameter `l` is `0`. Then left translation by `g₀` preserves the
discrete series coefficient `l.dsCoeff`. -/
lemma dsCoeff_mul_eq_of_sub_one_eq_inclMatrix {σ : X → n} (hσ_sign : ∀ i : X, ε (σ i) = 1)
    (hσ_weight : ∀ i : X, l.lowestKType (σ i) = 0) {x : Matrix X X ℂ} {g₀ : USign ε}
    (hg₀ : (g₀ : Matrix n n ℂ) - 1 = inclMatrix ℂ σ * (x * (inclMatrix ℂ σ)ᴴ)) (g : USign ε) :
    l.dsCoeff (g₀ * g : USign ε) = l.dsCoeff g := by
  -- The matrix `g₀` is block diagonal both for the signs and for the weight.
  have hg₀_det : (g₀ : Matrix n n ℂ).det ≠ 0 := (g₀ : GL n ℂ).det_ne_zero
  have h_minors (y : Matrix n n ℂ) :
      weightMinors l.lowestKType (g₀ * y) = weightMinors l.lowestKType y :=
    weightMinors_mul_eq_of_zero_weight_block hg₀_det
      (fun i j hij ↦ apply_eq_zero_of_sub_one_eq_inclMatrix hσ_weight hg₀ hij)
      (sub_one_apply_eq_zero_of_weight_ne_zero hσ_weight hg₀) y
  have h_compact : blockDiagPart ε ((g₀ : Matrix n n ℂ) * g) = g₀ * blockDiagPart ε g :=
    blockDiagPart_mul_left (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hσ_sign hg₀) _
  have h_quot : (blockDiagPart ε ((g₀ : Matrix n n ℂ) * g))⁻¹ * ((g₀ : Matrix n n ℂ) * g) =
      (blockDiagPart ε g)⁻¹ * g := by
    rw [h_compact, Matrix.mul_inv_rev, mul_assoc, nonsing_inv_mul_cancel_left _ _ hg₀_det.isUnit]
  rw [Subgroup.coe_mul, Units.val_mul, dsCoeff, dsCoeff, h_quot, h_compact]
  simp only [flenstedJensen, mul_assoc (g₀ : Matrix n n ℂ), h_minors]

/-- Left translation by a block diagonal element `g₀` of `U(ε)` preserves the Frobenius norm of the
noncompact part. -/
lemma norm_noncompactPart_mul_of_mem_blockDiagAlg {g₀ : USign ε}
    (hg₀ : (g₀ : Matrix n n ℂ) ∈ blockDiagAlg ε) (g : USign ε) :
    ‖noncompactPart ε (g₀ * g : USign ε)‖ = ‖noncompactPart ε g‖ := by
  have hg₀_unitary : (g₀ : Matrix n n ℂ) ∈ unitaryGroup n ℂ :=
    U_one_mem_unitaryGroup ⟨(g₀ : GL n ℂ), mem_maxCompactU.2 hg₀⟩
  have h_mul : noncompactPart ε (g₀ * g : USign ε) = g₀ * noncompactPart ε g := by
    rw [noncompactPart, noncompactPart, Subgroup.coe_mul, Units.val_mul,
      blockDiagPart_mul_left hg₀, mul_sub]
  rw [h_mul, frobenius_norm_mul_of_unitary (mem_unitaryGroup_iff'.1 hg₀_unitary)]

/-! ### Decay away from the maximal compact subgroup -/

/-- For nonnegative reals `μ i`, one has `1 + ∑ μ i ≤ ∏ (1 + μ i)`. -/
lemma one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ i : ι, 0 ≤ μ i) :
    1 + ∑ i ∈ s, μ i ≤ ∏ i ∈ s, (1 + μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    nlinarith [hμ a, s.sum_nonneg fun i _ ↦ hμ i]

/-- For a complex square matrix `A` with its Frobenius norm, `1 + ‖A‖² ≤ |det (1 + Aᴴ A)|`. -/
lemma one_add_norm_sq_le_norm_det_one_add (A : Matrix n n ℂ) :
    1 + ‖A‖ ^ 2 ≤ ‖(1 + Aᴴ * A).det‖ := by
  -- In terms of the eigenvalues `μ i ≥ 0` of `Aᴴ * A` this is `1 + ∑ μ i ≤ ∏ (1 + μ i)`.
  have hA : (Aᴴ * A).PosSemidef := A.posSemidef_conjTranspose_mul_self
  let μ : n → ℝ := hA.isHermitian.eigenvalues
  have hμ (i : n) : 0 ≤ μ i := hA.eigenvalues_nonneg i
  have h_sum : ‖A‖ ^ 2 = ∑ i : n, μ i := by
    rw [← ofReal_inj, ← trace_star_mul_self_eq_norm_sq, hA.isHermitian.trace_eq_sum_eigenvalues]
    simp [μ]
  have h_prod : ‖(1 + Aᴴ * A).det‖ = ∏ i : n, (1 + μ i) :=
    calc ‖(1 + Aᴴ * A).det‖ = ‖(Aᴴ * A).charpoly.eval (-1)‖ := by
          rw [eval_charpoly, map_neg, map_one, ← neg_add', det_neg]
          simp
      _ = ∏ i : n, ‖(-1 : ℂ) - μ i‖ := by
          simp [μ, hA.isHermitian.charpoly_eq, Polynomial.eval_prod]
      _ = ∏ i : n, (1 + μ i) := prod_congr rfl fun i _ ↦ by
          rw [← neg_add', norm_neg, ← ofReal_one, ← ofReal_add,
            Complex.norm_of_nonneg (add_nonneg zero_le_one (hμ i))]
  simpa [h_sum, h_prod] using one_add_sum_le_prod_one_add Finset.univ hμ

/-- The part of `gᴴ ε g = ε` that commutes with `ε` reads `aᴴ a = 1 + yᴴ y`, for the compact part
`a = blockDiagPart ε g` and the noncompact part `y = noncompactPart ε g`. -/
lemma conjTranspose_blockDiagPart_mul_blockDiagPart (g : USign ε) :
    (blockDiagPart ε g)ᴴ * blockDiagPart ε g =
      1 + (noncompactPart ε g)ᴴ * noncompactPart ε g := by
  -- With `g' = ε g ε` one has `a = (g + g') / 2`, `y = (g - g') / 2` and `gᴴ g' = g'ᴴ g = 1`.
  set g' : Matrix n n ℂ := signMatrix ε * g * signMatrix ε with hg'
  have h_right : (g : Matrix n n ℂ)ᴴ * g' = 1 := by
    rw [hg', ← mul_assoc, ← mul_assoc, mem_U.1 g.2, signMatrix_mul_self]
  have h_left : g'ᴴ * (g : Matrix n n ℂ) = 1 := by simpa using congrArg conjTranspose h_right
  simp only [noncompactPart, blockDiagPart_eq, ← hg', conjTranspose_sub, conjTranspose_smul,
    conjTranspose_add, star_inv₀, star_ofNat, mul_add, add_mul, mul_sub, sub_mul, smul_add,
    smul_mul_assoc, mul_smul_comm, h_left, h_right]
  module

/-- Let the doubled Harish-Chandra parameter `l : HCParam ε` satisfy `l.HasLargeGap h`, i.e. have
gap `c = 500 (card n)³ + h`: its entries are distinct, have the parity of `card n - 1`, and differ
by at least `2 c` where the signs `ε` differ. Then for `g` in `USign ε`, the unitary group of
`diag ε`, `‖l.dsCoeff g‖ ^ 4` is at most `(1 + ‖y‖²)⁻¹ ^ h`, where the noncompact part
`y = noncompactPart ε g` keeps the entries `g i j` with `ε i ≠ ε j` and is zero elsewhere. -/
lemma norm_dsCoeff_pow_four_le {h : ℕ} [hg : l.HasLargeGap h] (g : USign ε) :
    ‖l.dsCoeff g‖ ^ 4 ≤ (1 + ‖noncompactPart ε g‖ ^ 2)⁻¹ ^ h := by
  set y : Matrix n n ℂ := noncompactPart ε g with hy
  have h_det : 1 + ‖y‖ ^ 2 ≤ ‖(blockDiagPart ε g).det‖ ^ 2 := by
    calc 1 + ‖y‖ ^ 2 ≤ ‖(1 + yᴴ * y).det‖ := one_add_norm_sq_le_norm_det_one_add y
      _ = ‖(blockDiagPart ε g).det‖ ^ 2 := by
          rw [hy, ← conjTranspose_blockDiagPart_mul_blockDiagPart, det_mul, det_conjTranspose,
            norm_mul, norm_star, sq]
  have h_coeff : ‖l.dsCoeff g‖ ^ 2 ≤ 1 / ‖(blockDiagPart ε g).det‖ ^ h :=
    (le_div_iff₀ (by simp)).2 (norm_dsCoeff_sq_mul_det_pow_le_one hg le_add_self g)
  calc ‖l.dsCoeff g‖ ^ 4 = (‖l.dsCoeff g‖ ^ 2) ^ 2 := by ring
    _ ≤ (1 / ‖(blockDiagPart ε g).det‖ ^ h) ^ 2 := by gcongr
    _ = (‖(blockDiagPart ε g).det‖ ^ 2)⁻¹ ^ h := by simp [sq, mul_pow]
    _ ≤ (1 + ‖y‖ ^ 2)⁻¹ ^ h := by gcongr

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, and let
`j : S →* U(ε) × U(η)` (`U(ε) = USign ε`) satisfy `IsLaplaceDatum` for the splitting
`e : X ⊕ Fin M ≃ n` and the map `τ : X → m`. Then the weights `μ`, `μ'` of the lowest `K`-types of
`l` and `k` are `0` on the images of `X` under `e` and `τ`. Elsewhere `μ` is in `[-3 B, -B]`. `μ'`
is nonnegative, and at most `3 B` if `η` takes both signs. For `(g, g') = j s` the number
`φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is imaginary. Assume `1 ≤ B`. The rows of
`g - 1 = (subOnePair j s).1` off `X` have squared norm at most `6 (‖y‖² + ‖y'‖²)`. Here
`y = noncompactPart ε g` and `y' = noncompactPart η g'` keep the entries at indices of opposite
signs. -/
lemma IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le (hj : IsLaplaceDatum l k j τ B e φ)
    (hB : 1 ≤ B) (s : S) :
    ‖intDiagonal (offBlockIndicator e) * (subOnePair j s).1‖ ^ 2 ≤
      6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
  -- Sum the row relations of `g` with the weights `-l.lowestKType`, those of `g'` with the weights
  -- `k.lowestKType`, and add: the real parts of the traces cancel.
  have h_lower (i : n) : B * (offBlockIndicator e i : ℝ) ^ 2 ≤ (-l.lowestKType) i := by
    obtain ⟨x | a, rfl⟩ := e.surjective i
    · simp [offBlockIndicator, hj.weight_eq_zero]
    · simpa [offBlockIndicator, le_neg] using (hj.weight_mem a).2
  have h_upper (i : n) : ((-l.lowestKType) i : ℝ) ≤ 3 * B := by
    obtain ⟨x | a, rfl⟩ := e.surjective i
    · simpa [hj.weight_eq_zero] using zero_le_one.trans hB
    · simpa [neg_le] using (hj.weight_mem a).1
  have h_fst : B * ‖intDiagonal (offBlockIndicator e) * (subOnePair j s).1‖ ^ 2 -
        2 * (intDiagonal l.lowestKType * (subOnePair j s).1).trace.re ≤
      2 * (3 * B) * ‖noncompactPart ε (j s).1‖ ^ 2 := by
    simpa [← diagonal_neg, ← sub_eq_add_neg] using
      norm_sq_add_re_trace_le (j s).1 B (3 * B) (offBlockIndicator e) (-l.lowestKType) h_lower
        fun i _ _ ↦ h_upper i
  have h_snd : 2 * (intDiagonal k.lowestKType * (subOnePair j s).2).trace.re ≤
      2 * (3 * B) * ‖noncompactPart η (j s).2‖ ^ 2 := by
    simpa using norm_sq_add_re_trace_le (j s).2 0 (3 * B) 0 k.lowestKType
      (fun i ↦ by simpa using (hj.weight_nonneg_and_le i i).1)
      fun i i' ↦ (hj.weight_nonneg_and_le i i').2
  -- The two weighted traces differ by `φ s`, which is imaginary.
  have h_traces : (intDiagonal l.lowestKType * (subOnePair j s).1).trace.re =
      (intDiagonal k.lowestKType * (subOnePair j s).2).trace.re := by
    rw [← sub_eq_zero, ← sub_re, ← hj.re_phase_eq_zero s, ← hj.phase_eq s, phase]
  exact le_of_mul_le_mul_left (by linarith) (zero_lt_one.trans_le hB)

/-- In the setting of `IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le`, let `(g, g') = j s`.
The columns of `g - 1 = (subOnePair j s).1` off `X` have squared norm at most `6 (‖y‖² + ‖y'‖²)`,
for the noncompact parts `y = noncompactPart ε g` and `y' = noncompactPart η g'`. -/
lemma IsLaplaceDatum.norm_subOnePair_mul_intDiagonal_sq_le (hj : IsLaplaceDatum l k j τ B e φ)
    (hB : 1 ≤ B) (s : S) :
    ‖(subOnePair j s).1 * intDiagonal (offBlockIndicator e)‖ ^ 2 ≤
      6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
  -- Apply the bound for the rows to `g⁻¹ = ε gᴴ ε`.
  have h_inv : intDiagonal (offBlockIndicator e) * (subOnePair j s⁻¹).1 =
      signMatrix ε * ((subOnePair j s).1 * intDiagonal (offBlockIndicator e))ᴴ * signMatrix ε := by
    simp only [map_inv, Prod.fst_inv, U.coe_inv (signMatrix_mul_self ε) (j s).1]
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · rcases units_eq_one_or (ε a) with ha | ha <;> simp [signMatrix, ha, mul_comm]
    · simp [signMatrix, hab, mul_comm, mul_left_comm]
  calc ‖(subOnePair j s).1 * intDiagonal (offBlockIndicator e)‖ ^ 2
      = ‖intDiagonal (offBlockIndicator e) * (subOnePair j s⁻¹).1‖ ^ 2 := by
        rw [h_inv, norm_signMatrix_mul_conjTranspose_mul_signMatrix]
    _ ≤ 6 * (‖noncompactPart ε (j s⁻¹).1‖ ^ 2 + ‖noncompactPart η (j s⁻¹).2‖ ^ 2) :=
        hj.norm_intDiagonal_mul_subOnePair_sq_le hB s⁻¹
    _ = 6 * (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) := by
        rw [map_inv, Prod.fst_inv, Prod.snd_inv, norm_noncompactPart_inv,
          norm_noncompactPart_inv]

/-- Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, and let
`j : S →* U(ε) × U(η)` satisfy `IsLaplaceDatum`. Its image then contains `U(X)`, placed by
`e : X ⊕ Fin M ≃ n` in the first factor and by `τ : X → m` in the second, on indices where the sign
is `+1` and the weight of the lowest `K`-type is `0`; the bounds on the weights in terms of `B` are
not used. Let `u ∈ U(X)`. For each `s` there is `t` such that the block `onBlock e` on `X` of the
first component of `j t` is `u` times that of `j s`, while `laplaceIntegrand` and the norms of both
noncompact parts agree at `s` and `t`. -/
lemma IsLaplaceDatum.exists_laplaceIntegrand_eq_and_onBlock_eq (hj : IsLaplaceDatum l k j τ B e φ)
    {u : Matrix X X ℂ} (hu : u ∈ unitaryGroup X ℂ) (s : S) :
    ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
      onBlock e (j t).1 = u * onBlock e (j s).1 ∧
      ‖noncompactPart ε (j t).1‖ = ‖noncompactPart ε (j s).1‖ ∧
      ‖noncompactPart η (j t).2‖ = ‖noncompactPart η (j s).2‖ := by
  -- Take `t = s₀ s`, where `j s₀` is the diagonal copy of `u`.
  obtain ⟨s₀, hs₀⟩ := hj.exists_diagonal u hu
  obtain ⟨hs₀_fst, hs₀_snd⟩ :
      ((j s₀).1 : Matrix n n ℂ) - 1 =
          inclMatrix ℂ (e ∘ .inl) * ((u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ) ∧
        ((j s₀).2 : Matrix m m ℂ) - 1 = inclMatrix ℂ τ * ((u - 1) * (inclMatrix ℂ τ)ᴴ) := by
    simpa [Matrix.mul_assoc] using hs₀
  have hτ_sign (x : X) : η (τ x) = 1 := (hj.sign_weight_right x).1
  have hτ_weight (x : X) : k.lowestKType (τ x) = 0 := (hj.sign_weight_right x).2
  have h_phase : φ s₀ = 0 := by
    simp [← hj.phase_eq, phase, intDiagonal_mul_sub_one_eq_zero hj.weight_eq_zero hs₀_fst,
      intDiagonal_mul_sub_one_eq_zero hτ_weight hs₀_snd]
  have h_coeff_fst : l.dsCoeff (j (s₀ * s)).1 = l.dsCoeff (j s).1 := by
    rw [map_mul]
    exact dsCoeff_mul_eq_of_sub_one_eq_inclMatrix hj.sign_inl hj.weight_eq_zero hs₀_fst _
  have h_coeff_snd : k.dsCoeff (j (s₀ * s)).2 = k.dsCoeff (j s).2 := by
    rw [map_mul]
    exact dsCoeff_mul_eq_of_sub_one_eq_inclMatrix hτ_sign hτ_weight hs₀_snd _
  refine ⟨s₀ * s, ?_, ?_, ?_, ?_⟩
  · rw [laplaceIntegrand, laplaceIntegrand, h_coeff_fst, h_coeff_snd, hj.phase_mul, h_phase,
      zero_add]
  · rw [map_mul, Prod.fst_mul, Subgroup.coe_mul, Units.val_mul, eq_add_of_sub_eq hs₀_fst]
    ext x y
    simp [inclMatrix, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_apply, one_apply, sub_mul]
  · rw [map_mul]
    exact norm_noncompactPart_mul_of_mem_blockDiagAlg
      (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hj.sign_inl hs₀_fst) _
  · rw [map_mul]
    exact norm_noncompactPart_mul_of_mem_blockDiagAlg
      (mem_blockDiagAlg_of_sub_one_eq_inclMatrix hτ_sign hs₀_snd) _

/-- Let `j` satisfy `IsLaplaceDatum`, of which only `tr (g - 1) = tr (g' - 1)` is used. For
`(g, g') = j s` with noncompact parts `y = noncompactPart ε g` and `y' = noncompactPart η g'`, one
has `‖g' - 1‖² = ‖g - 1‖² - 2 ‖y‖² + 2 ‖y'‖²`. -/
lemma IsLaplaceDatum.norm_snd_sq (hj : IsLaplaceDatum l k j τ B e φ) (s : S) :
    ‖(subOnePair j s).2‖ ^ 2 =
      ‖(subOnePair j s).1‖ ^ 2 - 2 * ‖noncompactPart ε (j s).1‖ ^ 2 +
        2 * ‖noncompactPart η (j s).2‖ ^ 2 := by
  linarith [norm_sub_one_sq (j s).1, norm_sub_one_sq (j s).2,
    congrArg Complex.re (hj.trace_eq s)]

/-- **Localization.** Let `l`, `k` be doubled Harish-Chandra parameters for the signs `ε`, `η`, with
weights `μ`, `μ'` of the lowest `K`-types, and let `j : S →* U(ε) × U(η)` satisfy `IsLaplaceDatum`:
its image contains `U(X)` diagonally on indices of weight `0`; for `(g, g') = j s` the traces of
`g - 1` and `g' - 1` agree and `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is imaginary and additive
in `s`; `μ` lies in `[-3 B, -B]` off `X` and `μ'` is nonnegative and, if `η` takes both signs, at
most `3 B`. Let `1 ≤ B`, so that `μ` is negative off `X`, and `0 < r ≤ 1 / 6`. If the noncompact
parts `y`, `y'` of the components of `j s` have `‖y‖² + ‖y'‖² ≤ r²`, then `laplaceIntegrand` has the
same value at `s` and at some `t` such that both components of `subOnePair j t = j t - 1` have
Frobenius norm at most `4 r`. -/
lemma IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le
    (hj : IsLaplaceDatum l k j τ B e φ) (r : ℝ) (hB : 1 ≤ B)
    (hr_pos : 0 < r) (hr_small : r ≤ 6⁻¹) (s : S)
    (hs : ‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2 ≤ r ^ 2) :
    ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
      ‖(subOnePair j t).1‖ ≤ 4 * r ∧
      ‖(subOnePair j t).2‖ ≤ 4 * r := by
  -- The block `a` of `(j s).1` on `X` is almost unitary, hence invertible as `r ≤ 1 / 6`. After
  -- translation by the inverse of its unitary part, the block on `X` is near `1`; the translation
  -- keeps the norms of the noncompact parts, so the rows and columns off `X` are still near those
  -- of `1`. The equality of the traces then bounds the second component.
  set a : Matrix X X ℂ := onBlock e (j s).1
  have h_gram : ‖aᴴ * a - 1‖ ≤ 6 * r ^ 2 :=
    calc ‖aᴴ * a - 1‖ ≤ ‖intDiagonal (offBlockIndicator e) * (subOnePair j s).1‖ ^ 2 :=
          norm_onBlock_gram_sub_one_le e hj.sign_inl (j s).1
      _ ≤ 6 * r ^ 2 := by linarith [hj.norm_intDiagonal_mul_subOnePair_sq_le hB s]
  have h_six : 6 * r ^ 2 ≤ r := by nlinarith
  have ha_unit : IsUnit a := by
    have h_small : ‖1 - aᴴ * a‖ < 1 := by linarith [norm_sub_rev (1 : Matrix X X ℂ) (aᴴ * a)]
    have h_unit : IsUnit (aᴴ * a) := by simpa using isUnit_one_sub_of_norm_lt_one h_small
    exact isUnit_of_mul_isUnit_right h_unit
  -- Write `a = k₁ * z₁` with `k₁` unitary and `z₁` positive semidefinite.
  obtain ⟨k₁, hk₁, z₁, hz₁, h_polar⟩ := exists_unitary_mul_posSemidef ha_unit
  have hk₁_inv : k₁ᴴ * k₁ = 1 := mem_unitaryGroup_iff'.1 hk₁
  have hz₁_near : ‖z₁ - 1‖ ≤ r := by
    have h_sq : aᴴ * a = z₁ * z₁ := by
      rw [h_polar, conjTranspose_mul, hz₁.isHermitian.eq, mul_assoc, ← mul_assoc k₁ᴴ, hk₁_inv,
        one_mul]
    rw [h_sq] at h_gram
    linarith [norm_sub_one_le_norm_mul_self_sub_one hz₁]
  obtain ⟨t, h_value, h_block, hy, hy'⟩ :
      ∃ t : S, l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
        onBlock e (j t).1 = star k₁ * a ∧
        ‖noncompactPart ε (j t).1‖ = ‖noncompactPart ε (j s).1‖ ∧
        ‖noncompactPart η (j t).2‖ = ‖noncompactPart η (j s).2‖ :=
    hj.exists_laplaceIntegrand_eq_and_onBlock_eq (Unitary.star_mem hk₁) s
  have h_on : onBlock e (subOnePair j t).1 = z₁ - 1 := by
    calc onBlock e (subOnePair j t).1 = onBlock e (j t).1 - 1 := by ext x y; simp [one_apply]
      _ = k₁ᴴ * (k₁ * z₁) - 1 := by rw [h_block, ← h_polar, star_eq_conjTranspose]
      _ = z₁ - 1 := by rw [← mul_assoc, hk₁_inv, one_mul]
  rw [← hy, ← hy'] at hs
  -- The rows and the columns off `X` contribute `6 r²` each, the block on `X` contributes `r²`.
  have h_fst : ‖(subOnePair j t).1‖ ^ 2 ≤ 13 * r ^ 2 := by
    have h_block_le : ‖onBlock e (subOnePair j t).1‖ ^ 2 ≤ r ^ 2 := by rw [h_on]; gcongr
    linarith [norm_sq_le_rows_add_columns_add_block e (subOnePair j t).1,
      hj.norm_intDiagonal_mul_subOnePair_sq_le hB t, hj.norm_subOnePair_mul_intDiagonal_sq_le hB t]
  have h_snd : ‖(subOnePair j t).2‖ ^ 2 ≤ 15 * r ^ 2 := by
    linarith [hj.norm_snd_sq t, sq_nonneg ‖noncompactPart ε (j t).1‖]
  have h_root {x : ℝ} (hx : x ^ 2 ≤ 15 * r ^ 2) : x ≤ 4 * r :=
    le_of_sq_le_sq (by linarith [sq_nonneg r]) (by positivity)
  exact ⟨t, h_value, h_root (by linarith [sq_nonneg r]), h_root h_snd⟩

end New.DiscreteSeries

end Localization

end
