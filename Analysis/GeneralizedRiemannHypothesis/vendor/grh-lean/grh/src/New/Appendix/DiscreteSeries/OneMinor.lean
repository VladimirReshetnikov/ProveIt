import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import New.Appendix.DiscreteSeries.MinorSecondOrder

/-!
# One minor near the identity

Estimates for one principal minor `det_S`, in terms of the blocks that cross the set `S` of indices,
that is, the entries `(i, j)` with exactly one of `i`, `j` in `S`: its size on a unitary matrix
(`norm_principalMinor_sq_le_exp`), and its form on `kᴴ ĝ k` for `k` unitary and block diagonal and
`ĝ = reducedExp ε o Z` for a small `Z` in the Lie algebra of `U(J)`, with `o` injective and
`o i < o j` whenever `i ∈ S` and `j ∉ S` (`exists_principalMinor_conj_reducedExp_eq_cexp`): up to an
error, `exp (tr P Z + ‖[P, Z]‖² / 4)`, where `P` is the projection to `S` and `‖[P, Z]‖` is the norm
of the two blocks of `Z` that cross `S`. A third estimate for one minor is
`exists_det_one_add_proj_mul_eq_exp` in `New.Appendix.DiscreteSeries.MinorSecondOrder`.

The matrix `ĝ` differs from `exp Z` by unipotent factors. Block diagonal triangular factors multiply
Flensted-Jensen's coefficient by a character of their diagonal if the matrices involved are
accretive (`flenstedJensen_triangular_mul_mul_triangular`), so for small `Z` the coefficient is the
same at `ĝ` and at `exp Z` (`flenstedJensen_reducedExp`).

All norms of matrices are Frobenius norms, and `ε : n → ℤˣ` is a vector of signs. Notation:
* `principalMinor X p`, `coordProj p`: the principal minor `det_S X` and the diagonal projection for
  the set `S` of indices satisfying `p`.
* `blockDiagAlg ε`: the matrices that vanish at `(i, j)` whenever `ε i ≠ ε j`.
* `lowerMask ε o Z`: the matrix that keeps the entries `(i, j)` of `Z` with `o j < o i` and
  `ε i = ε j`.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work.
-/

open Matrix Finset Norms.Frobenius Complex ComplexConjugate ComplexOrder

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {o : n → ℤ}
  {A B P Q X Y Z k u : Matrix n n ℂ} {δ ζ : ℝ} {p : n → Prop} [DecidablePred p]

/-! ### The size of one minor -/

/-- The square of `|det Y|` is at most `exp (tr (Yᴴ Y - 1))`; this trace is real. -/
lemma norm_det_sq_le_exp (Y : Matrix n n ℂ) :
    ‖Y.det‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
  -- Use `x ≤ exp (x - 1)` on the eigenvalues `x ≥ 0` of `Yᴴ Y`.
  have hY : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
  have nonneg : ∀ i, 0 ≤ hY.eigenvalues i := eigenvalues_conjTranspose_mul_self_nonneg Y
  have trace_eq : (Yᴴ * Y - 1).trace.re = ∑ i, (hY.eigenvalues i - 1) := by
    rw [trace_sub, hY.trace_eq_sum_eigenvalues]
    simp
  calc ‖Y.det‖ ^ 2 = ‖(Yᴴ * Y).det‖ := by
        rw [det_mul, det_conjTranspose, norm_mul, norm_star, sq]
    _ = ∏ i, hY.eigenvalues i := by
        simp [hY.det_eq_prod_eigenvalues, abs_of_nonneg (nonneg _)]
    _ ≤ ∏ i, Real.exp (hY.eigenvalues i - 1) :=
        prod_le_prod₀ (fun i _ ↦ nonneg i) fun i _ ↦ by
          linarith [Real.add_one_le_exp (hY.eigenvalues i - 1)]
    _ = Real.exp (Yᴴ * Y - 1).trace.re := by rw [trace_eq, Real.exp_sum]

/-- The principal minor of `X` on the indices satisfying `p` is `det (1 + P (X - 1))`, where `P` is
the diagonal projection to these indices. -/
lemma principalMinor_eq_det_coordProj (X : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    principalMinor X p = (1 + coordProj p * (X - 1)).det := by
  rw [principalMinor_eq_det, coordProj, sub_eq_add_neg, ← mul_neg, neg_sub]

/-- For a unitary matrix `k` and an orthogonal projection `P`, the crossing block
`M = (1 - P) k P` satisfies `Mᴴ M = P - P kᴴ P k P`. -/
lemma conjTranspose_mul_self_one_sub_mul_mul (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P := by
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP_adj]
  linear_combination (norm := noncomm_ring) P * kᴴ * hPP * k * P + P * hk * P + hPP

/-- For a unitary matrix `k` and an orthogonal projection `P`, the Frobenius norms of the
commutator and of the block `(1 - P) k P` satisfy `‖[P, k]‖² = 2 ‖(1 - P) k P‖²`. -/
lemma norm_lie_sq_of_unitary (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ‖⁅P, k⁆‖ ^ 2 = 2 * ‖(1 - P) * k * P‖ ^ 2 := by
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  -- Both sides are `2 (tr P - tr (P kᴴ P k))`.
  have lie_eq : ⁅P, k⁆ᴴ * ⁅P, k⁆ = kᴴ * (P * k) - kᴴ * (P * k * P) - P * kᴴ * P * k + P := by
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hP_adj]
    linear_combination (norm := noncomm_ring) kᴴ * hPP * k + P * hk * P + hPP
  have trace_conj : (kᴴ * (P * k)).trace = P.trace := by
    rw [trace_mul_comm, mul_assoc, hk', mul_one]
  have trace_left : (kᴴ * (P * k * P)).trace = (P * kᴴ * P * k).trace := by
    simp only [← mul_assoc, trace_mul_comm _ P]
  have trace_right : (P * kᴴ * P * k * P).trace = (P * kᴴ * P * k).trace := by
    simp only [trace_mul_comm _ P, ← mul_assoc, hPP]
  have block_eq : ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P :=
    conjTranspose_mul_self_one_sub_mul_mul hP hk
  rw [← ofReal_inj, ofReal_mul, ← trace_star_mul_self_eq_norm_sq,
    ← trace_star_mul_self_eq_norm_sq, lie_eq, block_eq]
  simp only [trace_add, trace_sub, trace_conj, trace_left, trace_right, ofReal_ofNat]
  ring

/-- Size of one minor: let `k` be a unitary matrix, `S` the set of indices satisfying `p`, and
`P = coordProj p` the diagonal projection to `S`. Then the principal minor of `k` on `S` satisfies
`|det_S k|² ≤ exp (-‖[P, k]‖² / 2)`. -/
theorem norm_principalMinor_sq_le_exp (p : n → Prop) [DecidablePred p] (hk : kᴴ * k = 1) :
    ‖principalMinor k p‖ ^ 2 ≤ Real.exp (-(‖⁅coordProj p, k⁆‖ ^ 2 / 2)) := by
  -- With `M = (1 - P) k P` and `Y = (1 - P) + P k P` we have `det_S k = det Y` and
  -- `Yᴴ Y = (1 - P) + P kᴴ P k P = 1 - Mᴴ M`, while `‖[P, k]‖² = 2 ‖M‖²`.
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  set P : Matrix n n ℂ := coordProj p
  have hPP : P * P = P := hP.isIdempotentElem
  let M : Matrix n n ℂ := (1 - P) * k * P
  let Y : Matrix n n ℂ := 1 - P + P * k * P
  have minor_eq : principalMinor k p = Y.det := by
    have Y_eq : Y = 1 + P * (k - 1) * P := by
      simp [Y, mul_sub, sub_mul, hPP, sub_add_eq_add_sub, add_sub_assoc]
    rw [principalMinor_eq_det_coordProj, Y_eq, det_one_add_mul_comm (P * (k - 1)), ← mul_assoc, hPP]
  have Y_sq : Yᴴ * Y = 1 - P + P * kᴴ * P * k * P := by
    simp [Y, hP.isSelfAdjoint.star_eq, ← star_eq_conjTranspose, add_mul, mul_add, mul_sub, sub_mul,
      ← mul_assoc, mul_assoc _ P P, hPP]
  have gram_eq : Yᴴ * Y - 1 = -(Mᴴ * M) := by
    rw [Y_sq, conjTranspose_mul_self_one_sub_mul_mul hP hk]
    abel
  calc ‖principalMinor k p‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
        rw [minor_eq]
        exact norm_det_sq_le_exp Y
    _ = Real.exp (-‖M‖ ^ 2) := by
        rw [gram_eq, trace_neg, trace_star_mul_self_eq_norm_sq, neg_re, ofReal_re]
    _ = Real.exp (-(‖⁅P, k⁆‖ ^ 2 / 2)) := by
        rw [norm_lie_sq_of_unitary hP hk, mul_div_cancel_left₀ _ two_ne_zero]

/-! ### Unipotent factors -/

/-- Let the integer vector `o` order the indices, and let the matrix `u` be strictly lower
triangular for this order, that is, its entry `(i, j)` vanishes whenever `o i ≤ o j`. Then at these
positions the entry of `exp u` is the entry of the identity matrix. In particular, the diagonal
entries of `exp u` are `1`. -/
lemma exp_apply_eq_one_apply_of_le (hu : ∀ i j : n, o i ≤ o j → u i j = 0) {i j : n}
    (hij : o i ≤ o j) :
    NormedSpace.exp u i j = (1 : Matrix n n ℂ) i j := by
  -- The positive powers of `u` are strictly triangular, so only the first term of the series stays.
  have pow_apply_eq_zero (m : ℕ) : ∀ a b : n, o a ≤ o b → (u ^ (m + 1)) a b = 0 := by
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      intro a b hab
      rw [pow_succ, mul_apply]
      refine sum_eq_zero fun c _ ↦ ?_
      rcases le_total (o a) (o c) with hac | hca
      · rw [ih a c hac, zero_mul]
      · rw [hu c b (hca.trans hab), mul_zero]
  have entry_series : HasSum (fun m : ℕ ↦ ((m.factorial : ℂ)⁻¹ • u ^ m) i j)
      (NormedSpace.exp u i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) u) i) j
  have higher_term : ∀ m ≠ 0, ((m.factorial : ℂ)⁻¹ • u ^ m) i j = 0
    | 0, hm => absurd rfl hm
    | m + 1, _ => by rw [Matrix.smul_apply, pow_apply_eq_zero m i j hij, smul_zero]
  simpa using entry_series.unique (hasSum_single 0 higher_term)

/-- The entry `(i, j)` of `exp (-u)` with `o i ≤ o j` is that of the identity matrix, where
`u = lowerMask ε o Z` keeps the entries `(i, j)` of `Z` with `ε i = ε j` and `o j < o i`. -/
lemma exp_neg_lowerMask_apply_of_le (ε : n → ℤˣ) (Z : Matrix n n ℂ) {i j : n} (hij : o i ≤ o j) :
    NormedSpace.exp (-lowerMask ε o Z) i j = (1 : Matrix n n ℂ) i j := by
  exact exp_apply_eq_one_apply_of_le (fun a b hab ↦ by simp [hab.not_gt]) hij

/-- The matrix `exp (-u)` is block diagonal for the signs `ε`, where `u = lowerMask ε o Z` keeps
the entries `(i, j)` of `Z` with `ε i = ε j` and `o j < o i`. -/
lemma exp_neg_lowerMask_mem_blockDiagAlg (ε : n → ℤˣ) (o : n → ℤ) (Z : Matrix n n ℂ) :
    NormedSpace.exp (-lowerMask ε o Z) ∈ blockDiagAlg ε := by
  have block : -lowerMask ε o Z ∈ blockDiagAlg ε :=
    mem_blockDiagAlg.2 fun i j hij ↦ by simp [hij]
  exact mem_blockDiagAlg_iff_commute.2 (mem_blockDiagAlg_iff_commute.1 block).exp_right

/-- The matrix `exp (-u)` is invertible and lower triangular for the order `o`
(`IsBorelMatrix (-o)`), where `u = lowerMask ε o Z` keeps the entries `(i, j)` of `Z` with
`ε i = ε j` and `o j < o i`. -/
lemma isBorelMatrix_exp_neg_lowerMask (ε : n → ℤˣ) (o : n → ℤ) (Z : Matrix n n ℂ) :
    IsBorelMatrix (-o) (NormedSpace.exp (-lowerMask ε o Z)) := by
  refine ⟨fun i j hij ↦ ?_, by simp [det_exp]⟩
  have lt : o i < o j := neg_lt_neg_iff.1 hij
  rw [exp_neg_lowerMask_apply_of_le ε Z lt.le, one_apply_ne (ne_of_apply_ne o lt.ne)]

/-- The product `diagChar w (exp (-u)) = ∏ i, exp (-u) i i ^ w i` over the diagonal entries of
`exp (-u)` is `1`, where `u = lowerMask ε o Z` keeps the entries `(i, j)` of `Z` with `ε i = ε j`
and `o j < o i`. -/
lemma diagChar_exp_neg_lowerMask (ε : n → ℤˣ) (o w : n → ℤ) (Z : Matrix n n ℂ) :
    diagChar w (NormedSpace.exp (-lowerMask ε o Z)) = 1 := by
  exact prod_eq_one fun i _ ↦ by
    rw [exp_neg_lowerMask_apply_of_le ε Z le_rfl, one_apply_eq, _root_.one_zpow]

/-- The matrix `ĝ = exp (-u) exp Z exp (-v)`, where `u = lowerMask ε (-o) Z` and
`v = lowerMask ε o Z` are the strictly lower and strictly upper triangular parts, in the order of
decreasing `o`, of the block diagonal (compact) part of `Z` for the signs `ε`. -/
noncomputable def reducedExp (ε : n → ℤˣ) (o : n → ℤ) (Z : Matrix n n ℂ) : Matrix n n ℂ :=
  NormedSpace.exp (-lowerMask ε (-o) Z) * NormedSpace.exp Z * NormedSpace.exp (-lowerMask ε o Z)

/-- Let `ĝ = reducedExp ε o Z = exp (-u) exp Z exp (-v)`, where `u = lowerMask ε (-o) Z` and
`v = lowerMask ε o Z` keep the entries of `Z` at equal signs that are strictly triangular in the
one or the other direction for the order `o`. Then `det ĝ = exp (tr Z)`, as `u` and `v` have trace
`0`. -/
lemma det_reducedExp : (reducedExp ε o Z).det = cexp Z.trace := by
  have trace_zero (c : n → ℤ) : (-lowerMask ε c Z).trace = 0 := by simp [trace]
  simp only [reducedExp, det_mul, det_exp, trace_zero, exp_zero, one_mul, mul_one]

/-- If `X` and `Y` are within `ρ` and `σ` of the identity in the Frobenius norm, then their product
is within `ρ σ + ρ + σ` of it. -/

lemma norm_mul_sub_one_le {ρ σ : ℝ} (hX : ‖X - 1‖ ≤ ρ) (hY : ‖Y - 1‖ ≤ σ) :
    ‖X * Y - 1‖ ≤ ρ * σ + ρ + σ := by
  rw [show X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) by noncomm_ring]
  exact norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hX hY) hX) hY

/-- Let `ε` be a vector of signs; a matrix is block diagonal if its entry `(i, j)` vanishes whenever
`ε i ≠ ε j`. Let the integer vector `l = 2λ : HCParam ε` be a doubled Harish-Chandra parameter of
gap `h`: its entries are distinct and congruent to `card n - 1` mod 2, and `|λ i - λ j| ≥ h`
whenever `ε i ≠ ε j`. Let `Z` have Frobenius norm at most `1 / 20`. Flensted-Jensen's coefficient
`l.flenstedJensen 1 z` is the integral of `|m_Λ k|² / m_{-λ-ρ} (kᴴ z k)` over the group `K` of
unitary block diagonal matrices `k`, divided by the integral of `|m_Λ k|²`. Here `m_w` is the
product of principal minors `weightMinors w`, `Λ` is the highest weight of the lowest `K`-type, `ρ`
is the half sum of the roots positive for `l`, and the argument `1` is the matrix `g` in the general
numerator `m_Λ (g k) conj (m_Λ k)`. This coefficient takes the same value at `z = exp Z` and at
`z = reducedExp ε l Z = exp (-u) exp Z exp (-v)`. Here `u = lowerMask ε (-l) Z` keeps the entries
`(i, j)` of `Z` with `ε i = ε j` and `l i < l j`, and `v = lowerMask ε l Z` keeps those with
`ε i = ε j` and `l j < l i`. -/
lemma flenstedJensen_reducedExp {ε : n → ℤˣ} {Z : Matrix n n ℂ} {h : ℕ} {l : HCParam ε}
    (hl : l.HasGap h) (hZ : ‖Z‖ ≤ 1 / 20) :
    l.flenstedJensen 1 (reducedExp ε l Z) = l.flenstedJensen 1 (NormedSpace.exp Z) := by
  -- The matrices `exp Z` and `b' * exp Z * b` are near `1`, hence accretive.
  have near {A : Matrix n n ℂ} (hA : ‖A‖ ≤ ‖Z‖) : ‖NormedSpace.exp A - 1‖ ≤ 1 / 10 :=
    calc ‖NormedSpace.exp A - 1‖ ≤ 2 * ‖A‖ := norm_exp_sub_one_le (by linarith)
      _ ≤ 1 / 10 := by linarith
  have near_tri (c : n → ℤ) : ‖NormedSpace.exp (-lowerMask ε c Z) - 1‖ ≤ 1 / 10 :=
    near ((norm_neg _).trans_le norm_entryMask_le)
  set b' : Matrix n n ℂ := NormedSpace.exp (-lowerMask ε (-l) Z)
  set b : Matrix n n ℂ := NormedSpace.exp (-lowerMask ε l Z)
  have near_exp : ‖NormedSpace.exp Z - 1‖ ≤ 1 / 10 := near le_rfl
  have near_left : ‖b' * NormedSpace.exp Z - 1‖ ≤ 1 / 4 :=
    (norm_mul_sub_one_le (near_tri (-l)) near_exp).trans (by norm_num)
  have near_both : ‖b' * NormedSpace.exp Z * b - 1‖ ≤ 1 / 2 :=
    (norm_mul_sub_one_le near_left (near_tri l)).trans (by norm_num)
  have accretive {A : Matrix n n ℂ} (hA : ‖A - 1‖ ≤ 1 / 2) : A.IsAccretive :=
    isAccretive_of_norm_sub_one_lt (hA.trans_lt (by norm_num))
  have hb'_mem : b' ∈ blockDiagAlg ε := exp_neg_lowerMask_mem_blockDiagAlg ε (-l) Z
  have hb'_tri : IsBorelMatrix l b' := by
    simpa only [neg_neg] using isBorelMatrix_exp_neg_lowerMask ε (-l) Z
  have hb'_char : diagChar l.lowestKType b' = 1 :=
    diagChar_exp_neg_lowerMask ε (-l) l.lowestKType Z
  have hb_mem : b ∈ blockDiagAlg ε := exp_neg_lowerMask_mem_blockDiagAlg ε l Z
  have hb_tri : IsBorelMatrix (-l) b := isBorelMatrix_exp_neg_lowerMask ε l Z
  have hb_char : diagChar l.lowestKType b = 1 := diagChar_exp_neg_lowerMask ε l l.lowestKType Z
  rw [reducedExp, flenstedJensen_triangular_mul_mul_triangular hl hb'_mem hb'_tri hb_mem hb_tri
    (accretive (near_exp.trans (by norm_num))) (accretive near_both), hb'_char, hb_char, one_mul,
    one_mul]

/-- The absolute value of an entry of a matrix is at most the Frobenius norm of the matrix. -/

lemma norm_apply_le (X : Matrix n n ℂ) (i j : n) : ‖X i j‖ ≤ ‖X‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), frobenius_norm_sq_eq_sum]
  exact (single_le_sum (fun b _ ↦ sq_nonneg ‖X i b‖) (mem_univ j)).trans
    (single_le_sum (fun a _ ↦ sum_nonneg fun b _ ↦ sq_nonneg ‖X a b‖) (mem_univ i))

/-- The entry `(i, j)` of the commutator of `X` with the diagonal projection to the indices
satisfying `p` has the norm of `X i j` if exactly one of `p i`, `p j` holds, else it is `0`. -/
lemma norm_lie_coordProj_apply (X : Matrix n n ℂ) (i j : n) :
    ‖⁅coordProj p, X⁆ i j‖ = if p i ↔ p j then 0 else ‖X i j‖ := by
  by_cases hi : p i <;> by_cases hj : p j <;> simp [coordProj, Ring.lie_def, hi, hj]

/-- Keeping only the entries `(i, j)` with `r i j`, by `entryMask r`, commutes with taking the
commutator with the diagonal projection `coordProj p`. -/
lemma lie_coordProj_entryMask (r : n → n → Prop) [DecidableRel r] :
    ⁅coordProj p, entryMask r X⁆ = entryMask r ⁅coordProj p, X⁆ := by
  ext i j
  by_cases hij : r i j <;> simp [coordProj, Ring.lie_def, hij]

/-- Conjugation by a unitary matrix `k` moves an orthogonal projection `P` by `‖[P, k]‖`. -/
lemma norm_conj_sub_eq (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ‖k * P * kᴴ - P‖ = ‖⁅P, k⁆‖ := by
  have factor : k * P * kᴴ - P = -(k * ⁅P, k⁆ᴴ) := by
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      show Pᴴ = P from hP.isSelfAdjoint]
    linear_combination (norm := noncomm_ring) mul_eq_one_symm hk * P
  rw [factor, norm_neg, frobenius_norm_mul_of_unitary hk, ← star_eq_conjTranspose, norm_star]

/-- Let `A`, `P`, `Q` be complex square matrices, with the Frobenius norm. If `‖A‖ ≤ δ`, the norm of
the commutator `[P, A]` grows by at most `2 δ ‖Q - P‖` when `Q` replaces `P`. -/
lemma norm_lie_le_add {A P Q : Matrix n n ℂ} {δ : ℝ} (hA : ‖A‖ ≤ δ) :
    ‖⁅Q, A⁆‖ ≤ ‖⁅P, A⁆‖ + 2 * δ * ‖Q - P‖ :=
  calc ‖⁅Q, A⁆‖ = ‖⁅P, A⁆ + ((Q - P) * A - A * (Q - P))‖ := by
        simp only [Ring.lie_def]
        congr 1
        noncomm_ring
    _ ≤ ‖⁅P, A⁆‖ + (‖Q - P‖ * δ + δ * ‖Q - P‖) :=
        norm_add_le_of_le le_rfl
          (norm_sub_le_of_le (norm_mul_le_of_le le_rfl hA) (norm_mul_le_of_le hA le_rfl))
    _ = ‖⁅P, A⁆‖ + 2 * δ * ‖Q - P‖ := by ring

/-- Let `k` be a unitary matrix and let `P = coordProj p` be the diagonal projection to the indices
satisfying `p`. The absolute values of the diagonal entries of `k P kᴴ - P` have sum at most
`‖[P, k]‖²`, the squared Frobenius norm of the commutator. -/
lemma sum_norm_conj_coordProj_sub_le {k : Matrix n n ℂ} {p : n → Prop} [DecidablePred p]
    (hk : kᴴ * k = 1) :
    ∑ a : n, ‖(k * coordProj p * kᴴ - coordProj p) a a‖ ≤ ‖⁅coordProj p, k⁆‖ ^ 2 := by
  have factor : k * coordProj p * kᴴ - coordProj p = -(⁅coordProj p, k⁆ * kᴴ) := by
    rw [Ring.lie_def]
    linear_combination (norm := noncomm_ring) coordProj p * mul_eq_one_symm hk
  -- An entry of `[P, k]` is `0` or has the norm of the entry of `k`.
  have entry (a b : n) : ‖⁅coordProj p, k⁆ a b * kᴴ b a‖ = ‖⁅coordProj p, k⁆ a b‖ ^ 2 := by
    rw [norm_mul, norm_lie_coordProj_apply, conjTranspose_apply, norm_star]
    split_ifs <;> simp [sq]
  rw [factor, frobenius_norm_sq_eq_sum]
  refine sum_le_sum fun a _ ↦ ?_
  rw [Matrix.neg_apply, norm_neg, mul_apply]
  exact norm_sum_le_of_le _ fun b _ ↦ (entry a b).le

/-- Let `o` be injective, let `k` be unitary and block diagonal for the signs `ε`, and let
`‖Z‖ ≤ δ` in the Frobenius norm. Let `P = coordProj p` be the diagonal projection to the indices
satisfying `p`, and let `u = lowerMask ε (-o) Z` and `v = lowerMask ε o Z` be the two strictly
triangular parts of `Z` inside the blocks of `ε`. Then the trace of `k P kᴴ (-u + Z - v)` differs
from the trace of `P Z` by at most `δ ‖[P, k]‖²`. -/
lemma norm_trace_conj_coordProj_mul_sub_le (ho : o.Injective) (hZ_le : ‖Z‖ ≤ δ) (hk : kᴴ * k = 1)
    (hk_mem : k ∈ blockDiagAlg ε) :
    ‖(k * coordProj p * kᴴ * (-lowerMask ε (-o) Z + Z + -lowerMask ε o Z)).trace -
        (coordProj p * Z).trace‖ ≤
      δ * ‖⁅coordProj p, k⁆‖ ^ 2 := by
  -- Inside the blocks `Z - u - v` is diagonal, and `Q = k P kᴴ` vanishes outside the blocks, so
  -- only the diagonal of `Q` matters.
  set Q : Matrix n n ℂ := k * coordProj p * kᴴ with hQ
  have Q_mem : Q ∈ blockDiagAlg ε := by
    rw [hQ, ← inv_eq_left_inv hk]
    exact mul_mem (mul_mem hk_mem (diagonal_mem_blockDiagAlg _)) (blockDiagAlg.inv_mem hk_mem)
  set W : Matrix n n ℂ := -lowerMask ε (-o) Z + Z + -lowerMask ε o Z with hW
  have off_diagonal (a b : n) (hab : b ≠ a) : Q a b * W b a = 0 := by
    by_cases hε : ε a = ε b
    · rcases lt_or_gt_of_ne (ho.ne hab) with lt | lt <;> simp [hW, hε, lt, lt.not_gt]
    · simp [mem_blockDiagAlg.1 Q_mem a b hε]
  have trace_Q : (Q * W).trace = ∑ a : n, Q a a * Z a a := by
    refine sum_congr rfl fun a _ ↦ ?_
    rw [diag_apply, mul_apply, Fintype.sum_eq_single a (off_diagonal a)]
    simp [hW]
  have trace_P : (coordProj p * Z).trace = ∑ a : n, coordProj p a a * Z a a := by
    simp [coordProj, trace]
  calc ‖(Q * W).trace - (coordProj p * Z).trace‖
      = ‖∑ a, (Q - coordProj p) a a * Z a a‖ := by
        simp only [trace_Q, trace_P, ← sum_sub_distrib, Matrix.sub_apply, sub_mul]
    _ ≤ ∑ a, ‖(Q - coordProj p) a a‖ * δ :=
        norm_sum_le_of_le _ fun a _ ↦
          norm_mul_le_of_le le_rfl ((norm_apply_le Z a a).trans hZ_le)
    _ ≤ δ * ‖⁅coordProj p, k⁆‖ ^ 2 := by
        grw [← sum_mul, sum_norm_conj_coordProj_sub_le hk, mul_comm]
        exact (norm_nonneg _).trans hZ_le

/-- Multiplication on the right by an orthogonal projection does not increase the Frobenius
norm. -/

lemma norm_mul_proj_le {ρ : ℝ} (hP : IsStarProjection P) (hX : ‖X‖ ≤ ρ) : ‖X * P‖ ≤ ρ := by
  rw [← norm_star, star_mul, hP.isSelfAdjoint.star_eq]
  exact norm_proj_mul_le hP (by rwa [norm_star])

/-- The block `P A (1 - P)` of a matrix `A`, which maps the kernel of an orthogonal projection `P`
to its range, has Frobenius norm at most that of the commutator `[P, A] = P A - A P`. -/
lemma norm_cross_le (hP : IsStarProjection P) : ‖P * A * (1 - P)‖ ≤ ‖⁅P, A⁆‖ := by
  have hPP : P * P = P := hP.isIdempotentElem
  rw [show P * A * (1 - P) = P * ⁅P, A⁆ by
    rw [Ring.lie_def]
    linear_combination (norm := noncomm_ring) -hPP * A]
  exact norm_proj_mul_le hP le_rfl

/-- For an orthogonal projection `P`, consider the block `P A (1 - P)` of a matrix `A`, which maps
the kernel of `P` to its range. If `‖A‖ ≤ δ` in the Frobenius norm, then these blocks for two
orthogonal projections `P` and `Q` differ in Frobenius norm by at most `2 δ ‖Q - P‖`. -/
lemma norm_cross_sub_le (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hA : ‖A‖ ≤ δ) :
    ‖Q * A * (1 - Q) - P * A * (1 - P)‖ ≤ 2 * δ * ‖Q - P‖ :=
  calc ‖Q * A * (1 - Q) - P * A * (1 - P)‖
      = ‖(Q - P) * A * (1 - Q) - P * A * (Q - P)‖ := by
        congr 1
        noncomm_ring
    _ ≤ ‖(Q - P) * A * (1 - Q)‖ + ‖P * A * (Q - P)‖ := norm_sub_le _ _
    _ ≤ ‖Q - P‖ * δ + δ * ‖Q - P‖ :=
        add_le_add (norm_mul_proj_le hQ.one_sub (norm_mul_le_of_le le_rfl hA))
          (norm_mul_le_of_le (norm_proj_mul_le hP hA) le_rfl)
    _ = 2 * δ * ‖Q - P‖ := by ring

/-- Let `P` and `Q` be orthogonal projections and let `A` and `B` be matrices with `‖A‖, ‖B‖ ≤ δ`
and `‖[P, A]‖, ‖[Q, B]‖ ≤ ζ`. Then `crossTrace Q A B = tr (Q A (1 - Q) B)` differs from
`crossTrace P A B` by at most `4 δ ‖Q - P‖ ζ`. -/
lemma norm_crossTrace_sub_le (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hA : ‖A‖ ≤ δ)
    (hB : ‖B‖ ≤ δ) (hPA : ‖⁅P, A⁆‖ ≤ ζ) (hQB : ‖⁅Q, B⁆‖ ≤ ζ) :
    ‖crossTrace Q A B - crossTrace P A B‖ ≤ 4 * δ * ‖Q - P‖ * ζ := by
  -- The term is the trace of `R A (1 - R)` times `(1 - R) B R`, for `R = P` or `R = Q`.
  have crossTrace_eq {R : Matrix n n ℂ} (hR : IsStarProjection R) :
      crossTrace R A B = (R * A * (1 - R) * ((1 - R) * B * (1 - (1 - R)))).trace := by
    rw [sub_sub_cancel, ← mul_assoc, trace_mul_comm _ R]
    simp only [← mul_assoc, hR.isIdempotentElem.eq, mul_assoc _ (1 - R) (1 - R),
      hR.one_sub.isIdempotentElem.eq, crossTrace]
  have second_le : ‖(1 - Q) * B * (1 - (1 - Q))‖ ≤ ζ := by
    have lie_one_sub : ⁅1 - Q, B⁆ = -⁅Q, B⁆ := by simp only [Ring.lie_def]; noncomm_ring
    grw [norm_cross_le hQ.one_sub, lie_one_sub, norm_neg, hQB]
  have second_move : ‖(1 - Q) * B * (1 - (1 - Q)) - (1 - P) * B * (1 - (1 - P))‖ ≤
      2 * δ * ‖Q - P‖ := by
    simpa only [sub_sub_sub_cancel_left, norm_sub_rev P] using
      norm_cross_sub_le hP.one_sub hQ.one_sub hB
  calc ‖crossTrace Q A B - crossTrace P A B‖
      = ‖((Q * A * (1 - Q) - P * A * (1 - P)) * ((1 - Q) * B * (1 - (1 - Q)))).trace +
          (P * A * (1 - P) *
            ((1 - Q) * B * (1 - (1 - Q)) - (1 - P) * B * (1 - (1 - P)))).trace‖ := by
        rw [crossTrace_eq hP, crossTrace_eq hQ, sub_mul (Q * A * (1 - Q)), trace_sub,
          mul_sub (P * A * (1 - P)), trace_sub, sub_add_sub_cancel]
    _ ≤ 2 * δ * ‖Q - P‖ * ζ + ζ * (2 * δ * ‖Q - P‖) :=
        norm_add_le_of_le (norm_trace_mul_le (norm_cross_sub_le hP hQ hA) second_le)
          (norm_trace_mul_le ((norm_cross_le hP).trans hPA) second_move)
    _ = 4 * δ * ‖Q - P‖ * ζ := by ring

/-- Let `P` and `Q` be orthogonal projections, and let `A₁`, `A₂`, `A₃` be matrices of Frobenius
norm at most `δ` whose commutators with `P` and with `Q` have Frobenius norm at most `ζ`. Then
`crossTraceSum Q A₁ A₂ A₃`, the sum of `tr (Q Aᵢ (1 - Q) Aⱼ)` over `i ≤ j` with the terms `i = j`
halved, differs from `crossTraceSum P A₁ A₂ A₃` by at most `18 δ ‖Q - P‖ ζ`, with `‖Q - P‖` the
Frobenius norm. -/
lemma norm_crossTraceSum_sub_le {A₁ A₂ A₃ : Matrix n n ℂ} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hA₁ : ‖A₁‖ ≤ δ) (hA₂ : ‖A₂‖ ≤ δ) (hA₃ : ‖A₃‖ ≤ δ)
    (hP₁ : ‖⁅P, A₁⁆‖ ≤ ζ) (hP₂ : ‖⁅P, A₂⁆‖ ≤ ζ) (hP₃ : ‖⁅P, A₃⁆‖ ≤ ζ)
    (hQ₁ : ‖⁅Q, A₁⁆‖ ≤ ζ) (hQ₂ : ‖⁅Q, A₂⁆‖ ≤ ζ) (hQ₃ : ‖⁅Q, A₃⁆‖ ≤ ζ) :
    ‖crossTraceSum Q A₁ A₂ A₃ - crossTraceSum P A₁ A₂ A₃‖ ≤ 18 * δ * ‖Q - P‖ * ζ := by
  let move (A B : Matrix n n ℂ) : ℂ := crossTrace Q A B - crossTrace P A B
  let bound : ℝ := 4 * δ * ‖Q - P‖ * ζ
  have move_le {A B : Matrix n n ℂ} (hA : ‖A‖ ≤ δ) (hB : ‖B‖ ≤ δ) (hPA : ‖⁅P, A⁆‖ ≤ ζ)
      (hQB : ‖⁅Q, B⁆‖ ≤ ζ) : ‖move A B‖ ≤ bound :=
    norm_crossTrace_sub_le hP hQ hA hB hPA hQB
  calc ‖crossTraceSum Q A₁ A₂ A₃ - crossTraceSum P A₁ A₂ A₃‖
      = ‖(move A₁ A₁ + move A₂ A₂ + move A₃ A₃) / 2 +
          move A₁ A₂ + move A₁ A₃ + move A₂ A₃‖ := by
        simp only [crossTraceSum, move]
        ring_nf
    _ ≤ (‖move A₁ A₁‖ + ‖move A₂ A₂‖ + ‖move A₃ A₃‖) / 2 +
          ‖move A₁ A₂‖ + ‖move A₁ A₃‖ + ‖move A₂ A₃‖ := by
        grw [norm_add_le, norm_add₃_le, norm_div, norm_add₃_le, Complex.norm_two]
    _ ≤ 9 / 2 * bound := by
        linarith [move_le hA₁ hA₁ hP₁ hQ₁, move_le hA₂ hA₂ hP₂ hQ₂, move_le hA₃ hA₃ hP₃ hQ₃,
          move_le hA₁ hA₂ hP₁ hQ₂, move_le hA₁ hA₃ hP₁ hQ₃, move_le hA₂ hA₃ hP₂ hQ₃]
    _ = 18 * δ * ‖Q - P‖ * ζ := by ring

/-- For the coordinate projection `P` onto the indices satisfying `p`, the trace
`crossTrace P A B = tr (P A (1 - P) B)` is the sum of `A i j * B j i` over `i` inside and `j`
outside the set. -/
lemma crossTrace_coordProj :
    crossTrace (coordProj p) A B =
      ∑ i : n, ∑ j : n, if p i ∧ ¬p j then A i j * B j i else 0 := by
  simp only [crossTrace, trace, diag_apply, mul_apply (M := coordProj p * A * (1 - coordProj p))]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  by_cases hi : p i <;> by_cases hj : p j <;> simp [coordProj, mul_sub, hi, hj]

/-- Let `P` be the coordinate projection onto the indices satisfying `p`. Passing from `Z` to
`-lowerMask ε o Z`, minus its strictly triangular part for the order `o` inside the blocks of `ε`,
does not increase the Frobenius norm of the commutator with `P`. -/
lemma norm_lie_coordProj_neg_lowerMask_le :
    ‖⁅coordProj p, -lowerMask ε o Z⁆‖ ≤ ‖⁅coordProj p, Z⁆‖ := by
  have lie_eq : ⁅coordProj p, -lowerMask ε o Z⁆ = -⁅coordProj p, lowerMask ε o Z⁆ := by
    simp only [Ring.lie_def, mul_neg, neg_mul, neg_sub']
  rw [lie_eq, norm_neg, lie_coordProj_entryMask]
  exact norm_entryMask_le

/-- Let `Z` lie in the Lie algebra of `U(J)`, where `J` is the diagonal matrix of the signs `ε`.
Then `Z` is skew-Hermitian on the entries at equal signs (the compact part) and Hermitian on the
entries at opposite signs (the noncompact part). -/
lemma apply_of_mem_unitaryLie (hZ : Z ∈ unitaryLie (signMatrix ε)) (i j : n) :
    Z i j = if ε i = ε j then -conj (Z j i) else conj (Z j i) := by
  have lie_eq : Zᴴ * signMatrix ε + signMatrix ε * Z = 0 := hZ
  have entry : conj (Z j i) * ε j + ε i * Z i j = 0 := by
    simpa [signMatrix] using congrFun₂ lie_eq i j
  refine mul_left_cancel₀ (Int.cast_ne_zero.2 (ε j).ne_zero : ((ε j : ℤ) : ℂ) ≠ 0) ?_
  split_ifs with hε
  · rw [hε] at entry
    linear_combination entry
  · rw [Int.units_ne_iff_eq_neg.1 hε, Units.val_neg, Int.cast_neg] at entry
    linear_combination -entry

/-- Let `Z` lie in the Lie algebra of `U(J)`, that is, `Zᴴ J + J Z = 0`, where `J = signMatrix ε` is
the diagonal matrix of the signs `ε`. Let `P = coordProj p` be the diagonal projection to the set
`S` of indices satisfying `p`. Then the squared Frobenius norm `‖[P, Z]‖²` of the commutator is
twice the sum of `|Z j i|²` over `i` in `S` and `j` outside `S`, because `|Z i j| = |Z j i|`. -/
lemma norm_lie_coordProj_sq_of_mem_unitaryLie {ε : n → ℤˣ} {Z : Matrix n n ℂ} {p : n → Prop}
    [DecidablePred p] (hZ : Z ∈ unitaryLie (signMatrix ε)) :
    ‖⁅coordProj p, Z⁆‖ ^ 2 = 2 * ∑ i : n, ∑ j : n, if p i ∧ ¬p j then ‖Z j i‖ ^ 2 else 0 := by
  have norm_swap (i j : n) : ‖Z i j‖ = ‖Z j i‖ := by
    rw [apply_of_mem_unitaryLie hZ i j]
    split_ifs <;> simp
  have entry (i j : n) : ‖⁅coordProj p, Z⁆ i j‖ ^ 2 =
      (if p j ∧ ¬p i then ‖Z i j‖ ^ 2 else 0) + if p i ∧ ¬p j then ‖Z j i‖ ^ 2 else 0 := by
    rw [norm_lie_coordProj_apply, norm_swap j i]
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj]
  simp only [frobenius_norm_sq_eq_sum, entry, sum_add_distrib]
  rw [sum_comm, two_mul]

/-- Let `P = coordProj p` be the diagonal projection to the indices satisfying `p`, on which `o` is
smaller than on the other indices, and let `Z` lie in the Lie algebra of `U(J)`, where
`J = signMatrix ε` is the diagonal matrix of the signs `ε`. Let `(A₁, A₂, A₃) = (-u, Z, -v)`, where
`u = lowerMask ε (-o) Z` and `v = lowerMask ε o Z` are the two strictly triangular parts of `Z`
inside the blocks of `ε`. Then `crossTraceSum P A₁ A₂ A₃`, the sum of `tr (P Aᵢ (1 - P) Aⱼ)` over
`i ≤ j` with the terms `i = j` halved, is a quarter of the squared Frobenius norm of the
commutator `[P, Z]`. -/
lemma crossTraceSum_coordProj_eq (ho_lt : ∀ i j : n, p i → ¬p j → o i < o j)
    (hZ : Z ∈ unitaryLie (signMatrix ε)) :
    crossTraceSum (coordProj p) (-lowerMask ε (-o) Z) Z (-lowerMask ε o Z) =
      (‖⁅coordProj p, Z⁆‖ ^ 2 / 4 : ℝ) := by
  classical
  -- `compact` and `noncompact` are the squared norms of the entries of `Z` with row outside and
  -- column inside the set, at equal and at opposite signs. Each of the six terms is a combination
  -- of these two numbers.
  let part (q : n → n → Prop) : ℂ :=
    ∑ i : n, ∑ j : n, if p i ∧ ¬p j then (if q i j then (‖Z j i‖ : ℂ) ^ 2 else 0) else 0
  let compact : ℂ := part fun i j ↦ ε i = ε j
  let noncompact : ℂ := part fun i j ↦ ε i ≠ ε j
  have term {A B : Matrix n n ℂ} (c d : ℂ)
      (h_eq : ∀ i j : n, o i < o j → ε i = ε j → A i j * B j i = c * ‖Z j i‖ ^ 2)
      (h_ne : ∀ i j : n, ε i ≠ ε j → A i j * B j i = d * ‖Z j i‖ ^ 2) :
      crossTrace (coordProj p) A B = c * compact + d * noncompact := by
    simp only [crossTrace_coordProj, compact, noncompact, part, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    by_cases hij : p i ∧ ¬p j
    · by_cases hε : ε i = ε j <;> simp [hij, hε, h_eq i j (ho_lt i j hij.1 hij.2), h_ne i j]
    · simp [hij]
  have skew (i j : n) (hε : ε i = ε j) : Z i j * Z j i = -‖Z j i‖ ^ 2 := by
    rw [apply_of_mem_unitaryLie hZ i j, ite_eq_left hε, neg_mul, conj_mul']
  have hermitian (i j : n) (hε : ε i ≠ ε j) : Z i j * Z j i = ‖Z j i‖ ^ 2 := by
    rw [apply_of_mem_unitaryLie hZ i j, ite_eq_right hε, conj_mul']
  have term_self (c : n → ℤ) : crossTrace (coordProj p) (-lowerMask ε c Z) (-lowerMask ε c Z) =
      0 * compact + 0 * noncompact :=
    term 0 0 (fun i j _ _ ↦ by rcases le_total (c i) (c j) with le | le <;> simp [le.not_gt])
      fun i j hε ↦ by simp [hε]
  have term₂₂ : crossTrace (coordProj p) Z Z = -1 * compact + 1 * noncompact :=
    term (-1) 1 (fun i j _ hε ↦ by simp [skew i j hε]) fun i j hε ↦ by simp [hermitian i j hε]
  have term₁₂ : crossTrace (coordProj p) (-lowerMask ε (-o) Z) Z = 1 * compact + 0 * noncompact :=
    term 1 0 (fun i j lt hε ↦ by simp [lt, hε, skew i j hε]) fun i j hε ↦ by simp [hε]
  have term₂₃ : crossTrace (coordProj p) Z (-lowerMask ε o Z) = 1 * compact + 0 * noncompact :=
    term 1 0 (fun i j lt hε ↦ by simp [lt, hε, skew i j hε]) fun i j hε ↦ by simp [hε.symm]
  have term₁₃ : crossTrace (coordProj p) (-lowerMask ε (-o) Z) (-lowerMask ε o Z) =
      -1 * compact + 0 * noncompact :=
    term (-1) 0 (fun i j lt hε ↦ by simp [lt, hε, skew i j hε]) fun i j hε ↦ by simp [hε]
  have norm_sq_eq : ((‖⁅coordProj p, Z⁆‖ ^ 2 : ℝ) : ℂ) = 2 * (compact + noncompact) := by
    simp only [norm_lie_coordProj_sq_of_mem_unitaryLie hZ, compact, noncompact, part,
      ← sum_add_distrib, ofReal_mul, ofReal_sum]
    congr! 3 with i _ j _
    by_cases hε : ε i = ε j <;> simp [hε, apply_ite ofReal]
  rw [crossTraceSum, term_self, term_self, term₂₂, term₁₂, term₁₃, term₂₃, ofReal_div, norm_sq_eq,
    ofReal_ofNat]
  ring

/-- For a unitary matrix `k`, the principal minor of `kᴴ X k` on the indices satisfying `p` is
`det (1 + k P kᴴ (X - 1))`, where `P` is the coordinate projection onto these indices. -/
lemma principalMinor_conj_eq_det (hk : kᴴ * k = 1) :
    principalMinor (kᴴ * X * k) p = (1 + k * coordProj p * kᴴ * (X - 1)).det := by
  rw [principalMinor_eq_det_coordProj, mul_assoc k, mul_assoc k, det_one_add_mul_comm k]
  congr 1
  linear_combination (norm := noncomm_ring) coordProj p * hk

/-- For `δ, κ, ζ ≥ 0` and `ζ ≤ x + κ`, the error terms of
`exists_principalMinor_conj_reducedExp_eq_cexp` satisfy `δ κ² + 18 δ κ ζ + 10⁴ δ ζ² ≤ 10⁵ δ (x² +
κ²)`. -/
private lemma mul_sq_add_add_le_mul_sq_add_sq {x κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hζ : 0 ≤ ζ)
    (hζ_le : ζ ≤ x + κ) :
    δ * κ ^ 2 + 18 * δ * κ * ζ + 10 ^ 4 * δ * ζ ^ 2 ≤ 10 ^ 5 * δ * (x ^ 2 + κ ^ 2) :=
  calc δ * κ ^ 2 + 18 * δ * κ * ζ + 10 ^ 4 * δ * ζ ^ 2
      ≤ δ * κ ^ 2 + 18 * δ * κ * (x + κ) + 10 ^ 4 * δ * (x + κ) ^ 2 := by gcongr
    _ ≤ 10 ^ 5 * δ * (x ^ 2 + κ ^ 2) := by
        nlinarith [mul_nonneg hδ (sq_nonneg (x - κ)), mul_nonneg hδ (sq_nonneg x),
          mul_nonneg hδ (sq_nonneg κ)]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `o` be injective, let `S` be the set of indices satisfying `p`, on which `o` is smaller than
on the other indices, and let `P = coordProj p` be the coordinate projection onto `S`. Let `Z` lie
in the Lie algebra of `U(J)`, where `J = signMatrix ε` is the diagonal matrix of the signs `ε`, with
`‖Z‖ ≤ δ ≤ 1 / 20`, and let `k` be unitary and block diagonal for the signs `ε`. Then the principal
minor on `S` of `kᴴ ĝ k`, where `ĝ = reducedExp ε o Z = exp (-u) exp Z exp (-v)` for the two
strictly triangular parts `u`, `v` of `Z` inside the blocks of `ε`, is
`exp (tr (P Z) + ‖[P, Z]‖² / 4 + r)` with `‖r‖ ≤ 10⁵ δ (‖[P, Z]‖² + ‖[P, k]‖²)`. -/
theorem exists_principalMinor_conj_reducedExp_eq_cexp (ho : o.Injective)
    (ho_lt : ∀ i j : n, p i → ¬p j → o i < o j)
    (hZ : Z ∈ unitaryLie (signMatrix ε)) (hδ : δ ≤ 1 / 20) (hZ_le : ‖Z‖ ≤ δ) (hk : kᴴ * k = 1)
    (hk_mem : k ∈ blockDiagAlg ε) :
    ∃ r : ℂ, principalMinor (kᴴ * reducedExp ε o Z * k) p =
        cexp ((coordProj p * Z).trace + (‖⁅coordProj p, Z⁆‖ ^ 2 / 4 : ℝ) + r) ∧
      ‖r‖ ≤ 10 ^ 5 * δ * (‖⁅coordProj p, Z⁆‖ ^ 2 + ‖⁅coordProj p, k⁆‖ ^ 2) := by
  -- The minor is the determinant in `exists_det_one_add_proj_mul_eq_exp` for the three exponents
  -- `A₁`, `Z`, `A₃` of `ĝ` and `Q = k P kᴴ`, with `ζ = |[P, Z]| + 2 δ |[P, k]|`. The two sums in
  -- the exponent are compared with their values at `P` in place of `Q`.
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  set P : Matrix n n ℂ := coordProj p
  let Q : Matrix n n ℂ := k * P * kᴴ
  set x : ℝ := ‖⁅P, Z⁆‖
  set κ : ℝ := ‖⁅P, k⁆‖
  let ζ : ℝ := x + 2 * δ * κ
  let A₁ : Matrix n n ℂ := -lowerMask ε (-o) Z
  let A₃ : Matrix n n ℂ := -lowerMask ε o Z
  have hA₁ : ‖A₁‖ ≤ δ := (norm_neg _).trans_le (norm_entryMask_le.trans hZ_le)
  have hA₃ : ‖A₃‖ ≤ δ := (norm_neg _).trans_le (norm_entryMask_le.trans hZ_le)
  have hP₁ : ‖⁅P, A₁⁆‖ ≤ x := norm_lie_coordProj_neg_lowerMask_le
  have hP₃ : ‖⁅P, A₃⁆‖ ≤ x := norm_lie_coordProj_neg_lowerMask_le
  have hQ : IsStarProjection Q :=
    hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, hk, mul_eq_one_symm hk⟩)
  have hQP : ‖Q - P‖ = κ := norm_conj_sub_eq hP hk
  have hκ_nonneg : 0 ≤ κ := norm_nonneg _
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg Z).trans hZ_le
  have hx_le : x ≤ ζ := le_add_of_nonneg_right (by positivity)
  have hζ_le : ζ ≤ x + κ := add_le_add_right (mul_le_of_le_one_left hκ_nonneg (by linarith)) x
  have lie_Q_le {A : Matrix n n ℂ} (hA : ‖A‖ ≤ δ) (hPA : ‖⁅P, A⁆‖ ≤ x) : ‖⁅Q, A⁆‖ ≤ ζ := by
    grw [norm_lie_le_add (P := P) hA, hPA, hQP]
  let second (R : Matrix n n ℂ) : ℂ := crossTraceSum R A₁ Z A₃
  obtain ⟨rest, det_eq, rest_le⟩ : ∃ rest : ℂ,
      (1 + Q * (NormedSpace.exp A₁ * NormedSpace.exp Z * NormedSpace.exp A₃ - 1)).det =
          cexp ((Q * (A₁ + Z + A₃)).trace + second Q + rest) ∧
        ‖rest‖ ≤ 10 ^ 4 * δ * ζ ^ 2 :=
    exists_det_one_add_proj_mul_eq_exp hQ hδ hA₁ hZ_le hA₃ (lie_Q_le hA₁ hP₁)
      (lie_Q_le hZ_le le_rfl) (lie_Q_le hA₃ hP₃)
  have first_le : ‖(Q * (A₁ + Z + A₃)).trace - (P * Z).trace‖ ≤ δ * κ ^ 2 :=
    norm_trace_conj_coordProj_mul_sub_le ho hZ_le hk hk_mem
  have second_eq : second P = (x ^ 2 / 4 : ℝ) := crossTraceSum_coordProj_eq ho_lt hZ
  have second_le : ‖second Q - second P‖ ≤ 18 * δ * κ * ζ := by
    rw [← hQP]
    exact norm_crossTraceSum_sub_le hP hQ hA₁ hZ_le hA₃ (hP₁.trans hx_le) hx_le
      (hP₃.trans hx_le) (lie_Q_le hA₁ hP₁) (lie_Q_le hZ_le le_rfl) (lie_Q_le hA₃ hP₃)
  refine ⟨((Q * (A₁ + Z + A₃)).trace - (P * Z).trace) + (second Q - second P) + rest, ?_, ?_⟩
  · rw [principalMinor_conj_eq_det hk, reducedExp, det_eq, ← second_eq]
    congr 1
    ring
  · calc ‖((Q * (A₁ + Z + A₃)).trace - (P * Z).trace) + (second Q - second P) + rest‖
        ≤ δ * κ ^ 2 + 18 * δ * κ * ζ + 10 ^ 4 * δ * ζ ^ 2 :=
          norm_add_le_of_le (norm_add_le_of_le first_le second_le) rest_le
      _ ≤ 10 ^ 5 * δ * (x ^ 2 + κ ^ 2) :=
          mul_sq_add_add_le_mul_sq_add_sq hδ_nonneg hκ_nonneg ((norm_nonneg _).trans hx_le) hζ_le

end New.DiscreteSeries
