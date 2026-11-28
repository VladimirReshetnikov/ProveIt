import Lib.General.LinearAlgebra.MatricesNearIdentity

/-!
# One minor of a product of three exponentials, to second order

For an orthogonal projection `Q` and small matrices `A₁`, `A₂`, `A₃` we expand
`log det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` to second order. The rest vanishes to order three in
the `Aᵢ` and to order two in their parts that cross `Q`; Schwarz's lemma turns this into the bound
`O(δ ζ²)`, where `δ` bounds the `Aᵢ` and `ζ` bounds the commutators `⁅Q, Aᵢ⁆`. All norms are
Hilbert–Schmidt (Frobenius) norms, and no constant depends on the dimension.

The main result is `exists_det_one_add_proj_mul_eq_exp`. The order three is obtained by direct
estimates of the exponential series and of the integral that defines the logarithm. The rest
`logMinorRemainder` is a principal logarithm, holomorphic in the factor `τ` that scales the crossing
parts, and Schwarz's lemma is applied in `τ`.

Notions from other files:
* `logOneAdd M = ∫ s in 0..1, (1 + s M)⁻¹ M` is the matrix logarithm `log (1 + M)`, used for
  `‖M‖ ≤ 1 / 2`.
* `IsStarProjection Q` says that `Q` is an orthogonal projection: self-adjoint and idempotent.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work.
-/

noncomputable section

open Matrix Norms.Frobenius Complex

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {Q A A₁ A₂ A₃ L L' M S S' Y Y' : Matrix n n ℂ}
  {δ ζ ρ ρ' : ℝ}

/-! ### Expansion of a determinant to second order -/

/-- For a matrix `A` of Frobenius norm at most `1 / 2`, the exponential series after its terms of
order at most two is `A` times a matrix `R` of norm at most `‖A‖ ^ 2`. -/
lemma exists_exp_eq_add_mul (hA : ‖A‖ ≤ 1 / 2) :
    ∃ R : Matrix n n ℂ, NormedSpace.exp A = 1 + A + (2 : ℂ)⁻¹ • (A * A) + A * R ∧
      ‖R‖ ≤ ‖A‖ ^ 2 := by
  let term (k : ℕ) : Matrix n n ℂ := ((k + 3).factorial : ℂ)⁻¹ • A ^ (k + 2)
  have h_geometric : HasSum (fun k : ℕ ↦ ‖A‖ ^ 2 / 2 / 2 ^ k) (‖A‖ ^ 2) := hasSum_geometric_two' _
  have h_term (k : ℕ) : ‖term k‖ ≤ ‖A‖ ^ 2 / 2 / 2 ^ k :=
    calc ‖term k‖ ≤ 2⁻¹ * (‖A‖ ^ k * ‖A‖ ^ 2) := by
          rw [norm_smul, norm_inv, norm_natCast, ← pow_add]
          gcongr
          · exact_mod_cast Nat.factorial_le (show 2 ≤ k + 3 by omega)
          · exact norm_pow_le' A (by omega)
      _ ≤ 2⁻¹ * ((1 / 2) ^ k * ‖A‖ ^ 2) := by gcongr
      _ = ‖A‖ ^ 2 / 2 / 2 ^ k := by
          rw [_root_.one_div_pow]
          ring
  have h_summable : Summable term := .of_norm_bounded h_geometric.summable h_term
  refine ⟨∑' k, term k, ?_, tsum_of_norm_bounded h_geometric h_term⟩
  have h_tail : HasSum (fun k : ℕ ↦ ((k + 3).factorial : ℂ)⁻¹ • A ^ (k + 3))
      (A * ∑' k, term k) := by
    simpa only [term, mul_smul_comm, ← pow_succ'] using h_summable.hasSum.mul_left A
  have h_tail_exp : HasSum (fun k : ℕ ↦ ((k + 3).factorial : ℂ)⁻¹ • A ^ (k + 3))
      (NormedSpace.exp A - ∑ k ∈ Finset.range 3, (k.factorial : ℂ)⁻¹ • A ^ k) :=
    (hasSum_nat_add_iff' 3).2 (NormedSpace.exp_series_hasSum_exp' A)
  rw [← h_tail_exp.unique h_tail]
  simp [Finset.sum_range_succ, pow_two]

/-- For `‖M‖ ≤ 1 / 2` in Frobenius norm and `0 ≤ s ≤ 1`, the trace of `(1 + s M)⁻¹ M` is
`tr M - s tr M²` up to an error of at most `2 ‖M‖³`. -/
lemma norm_trace_inv_one_add_smul_mul_sub_le (hM : ‖M‖ ≤ 2⁻¹) {s : ℝ} (hs_nonneg : 0 ≤ s)
    (hs_le : s ≤ 1) :
    ‖((1 + s • M)⁻¹ * M).trace - (M.trace - s * (M * M).trace)‖ ≤ 2 * ‖M‖ ^ 3 := by
  -- With `V = (1 + s M)⁻¹` we have `V M = M - s M² + s² M² V M`.
  have h_smul : ‖s • M‖ ≤ ‖M‖ := norm_smul_le_of_le_one s le_rfl ⟨hs_nonneg, hs_le⟩
  set V : Matrix n n ℂ := (1 + s • M)⁻¹
  have h_small : ‖s • M‖ ≤ 2⁻¹ := h_smul.trans hM
  have h_near : ‖V - 1‖ ≤ 1 := by linarith [norm_inv_one_add_sub_one_le h_small]
  have h_expand : V * M - (M - s • M * M) = s • M * (s • M) * (V * M) := by
    have h_mul : (1 + s • M) * V = 1 := one_add_mul_inv_one_add (h_small.trans_lt two_inv_lt_one)
    generalize s • M = N at h_mul ⊢
    linear_combination (norm := noncomm_ring) (1 - N) * h_mul * M
  have hVM : ‖V * M‖ ≤ 2 * ‖M‖ :=
    calc ‖V * M‖ = ‖M + (V - 1) * M‖ := by rw [sub_one_mul, add_sub_cancel]
      _ ≤ 2 * ‖M‖ := by grw [norm_add_le, norm_mul_le, h_near, one_mul, two_mul]
  calc ‖(V * M).trace - (M.trace - s * (M * M).trace)‖
      = ‖(s • M * (s • M) * (V * M)).trace‖ := by
        rw [← h_expand, trace_sub, trace_sub, smul_mul_assoc, trace_smul, real_smul]
    _ ≤ ‖M‖ * ‖M‖ * (2 * ‖M‖) := norm_trace_mul_le (norm_mul_le_of_le h_smul h_smul) hVM
    _ = 2 * ‖M‖ ^ 3 := by ring

/-- For a matrix `M` of Frobenius norm at most `1 / 2`, the trace of the matrix logarithm
`logOneAdd M = log (1 + M)` is `tr M - tr M² / 2` up to an error of at most `2 ‖M‖³`. -/
lemma norm_trace_logOneAdd_sub_le (hM : ‖M‖ ≤ 2⁻¹) :
    ‖(logOneAdd M).trace - (M.trace - (M * M).trace / 2)‖ ≤ 2 * ‖M‖ ^ 3 := by
  -- Integrate the expansion of `tr ((1 + s M)⁻¹ M)` over `0 ≤ s ≤ 1`.
  have h_int : IntervalIntegrable (fun s : ℝ ↦ ((1 + s • M)⁻¹ * M).trace)
      MeasureTheory.volume 0 1 := by
    simpa only [one_mul] using intervalIntegrable_trace_mul_inv_one_add_smul_mul hM 1
  have h_log : ∫ s : ℝ in 0..1, ((1 + s • M)⁻¹ * M).trace = (logOneAdd M).trace := by
    simpa only [one_mul] using integral_trace_mul_inv_one_add_smul_mul hM 1
  have h_main : ∫ s : ℝ in 0..1, (M.trace - s * (M * M).trace) = M.trace - (M * M).trace / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    simp [div_eq_inv_mul]
  calc ‖(logOneAdd M).trace - (M.trace - (M * M).trace / 2)‖
      = ‖∫ s : ℝ in 0..1, (((1 + s • M)⁻¹ * M).trace - (M.trace - s * (M * M).trace))‖ := by
        rw [intervalIntegral.integral_sub h_int (Continuous.intervalIntegrable (by fun_prop) 0 1),
          h_log, h_main]
    _ ≤ 2 * ‖M‖ ^ 3 * |1 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ by
        rw [Set.uIoc_of_le zero_le_one] at hs
        exact norm_trace_inv_one_add_smul_mul_sub_le hM hs.1.le hs.2
    _ = 2 * ‖M‖ ^ 3 := by simp

/-- `IsExpansion Q Y L S ρ` says that `Y = L + S + ⋯` is an expansion in a small quantity `ρ`:
the term `L` is of first order, `Y - L` is of second order, and the rest `Y - L - S` is of third
order when measured by the trace against `Q`, which keeps the bound free of the dimension. -/
structure IsExpansion (Q Y L S : Matrix n n ℂ) (ρ : ℝ) : Prop where
  /-- The term `L` is of first order. -/
  norm_linear_le : ‖L‖ ≤ ρ
  /-- The difference `Y - L` is of second order. -/
  norm_sub_linear_le : ‖Y - L‖ ≤ ρ ^ 2
  /-- The trace of `Q` times the rest is of third order. -/
  norm_trace_rest_le : ‖(Q * (Y - L - S)).trace‖ ≤ ρ ^ 3

lemma IsExpansion.nonneg (h : IsExpansion Q Y L S ρ) : 0 ≤ ρ :=
  (norm_nonneg L).trans h.norm_linear_le

/-- If `Y = L + S + ⋯` is an expansion in `ρ ≤ 1 / 3`, so that `‖L‖ ≤ ρ` and `‖Y - L‖ ≤ ρ ^ 2`,
then `‖Y‖ ≤ 4 ρ / 3`. -/
lemma IsExpansion.norm_le (h : IsExpansion Q Y L S ρ) (hρ : ρ ≤ 1 / 3) : ‖Y‖ ≤ 4 / 3 * ρ :=
  calc ‖Y‖ ≤ ‖L‖ + ‖Y - L‖ := norm_le_norm_add_norm_sub' Y L
    _ ≤ ρ + ρ ^ 2 := add_le_add h.norm_linear_le h.norm_sub_linear_le
    _ ≤ 4 / 3 * ρ := by nlinarith [h.nonneg]

/-- For an orthogonal projection `Q` and `‖A‖ ≤ ρ ≤ 1 / 2` in Frobenius norm, the series
`exp A - 1 = A + A² / 2 + ⋯` is an expansion in `ρ`: `‖A‖ ≤ ρ`, `‖exp A - 1 - A‖ ≤ ρ ^ 2`, and the
trace of `Q` times the rest `exp A - 1 - A - A² / 2` has norm at most `ρ ^ 3`. -/
lemma isExpansion_exp (hQ : IsStarProjection Q) (hA : ‖A‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    IsExpansion Q (NormedSpace.exp A - 1) A ((2 : ℂ)⁻¹ • (A * A)) ρ := by
  obtain ⟨R, h_exp, hR_norm⟩ := exists_exp_eq_add_mul (hA.trans hρ)
  have hR : ‖R‖ ≤ ρ ^ 2 := hR_norm.trans (by gcongr)
  have h_rest : NormedSpace.exp A - 1 - A - (2 : ℂ)⁻¹ • (A * A) = A * R := by
    linear_combination (norm := abel) h_exp
  refine ⟨hA, ?_, ?_⟩
  · calc ‖NormedSpace.exp A - 1 - A‖ = ‖(2 : ℂ)⁻¹ • (A * A) + A * R‖ := by
          rw [← h_rest, add_sub_cancel]
      _ ≤ 2⁻¹ * (ρ * ρ) + 1 / 2 * ρ ^ 2 := by
          grw [norm_add_le, norm_smul, norm_mul_le_of_le hA hA, norm_mul_le_of_le (hA.trans hρ) hR]
          simp
      _ = ρ ^ 2 := by ring
  · calc ‖(Q * (NormedSpace.exp A - 1 - A - (2 : ℂ)⁻¹ • (A * A))).trace‖
        = ‖(Q * A * R).trace‖ := by rw [h_rest, mul_assoc]
      _ ≤ ρ * ρ ^ 2 := norm_trace_mul_le (norm_proj_mul_le hQ hA) hR
      _ = ρ ^ 3 := by ring

/-- Expansions multiply. Let `Q` be an orthogonal projection. Let `Y - 1 = L + S + ⋯` be an
expansion in `ρ ≤ 1 / 3`, that is, `‖L‖ ≤ ρ`, `‖Y - 1 - L‖ ≤ ρ²` and
`‖tr Q (Y - 1 - L - S)‖ ≤ ρ³`, and let `Y' - 1 = L' + S' + ⋯` be one in `ρ' ≤ 1 / 3`. Then
`Y Y' - 1 = (L + L') + (S + S' + L L') + ⋯` is an expansion in `ρ + ρ'`. -/
lemma IsExpansion.mul (hQ : IsStarProjection Q) (h : IsExpansion Q (Y - 1) L S ρ)
    (h' : IsExpansion Q (Y' - 1) L' S' ρ') (hρ : ρ ≤ 1 / 3) (hρ' : ρ' ≤ 1 / 3) :
    IsExpansion Q (Y * Y' - 1) (L + L') (S + S' + L * L') (ρ + ρ') := by
  have h_second : Y * Y' - 1 - (L + L') = (Y - 1 - L) + (Y' - 1 - L') + (Y - 1) * (Y' - 1) := by
    noncomm_ring
  have h_third : Q * (Y * Y' - 1 - (L + L') - (S + S' + L * L')) =
      Q * (Y - 1 - L - S) + Q * (Y' - 1 - L' - S') +
        Q * (Y - 1 - L) * (Y' - 1) + Q * L * (Y' - 1 - L') := by
    noncomm_ring
  refine ⟨norm_add_le_of_le h.norm_linear_le h'.norm_linear_le, ?_, ?_⟩
  · calc ‖Y * Y' - 1 - (L + L')‖ ≤ ρ ^ 2 + ρ' ^ 2 + 4 / 3 * ρ * (4 / 3 * ρ') := by
          grw [h_second, norm_add₃_le, h.norm_sub_linear_le, h'.norm_sub_linear_le,
            norm_mul_le_of_le (h.norm_le hρ) (h'.norm_le hρ')]
      _ ≤ (ρ + ρ') ^ 2 := by nlinarith [mul_nonneg h.nonneg h'.nonneg]
  · calc ‖(Q * (Y * Y' - 1 - (L + L') - (S + S' + L * L'))).trace‖
        ≤ ρ ^ 3 + ρ' ^ 3 + ρ ^ 2 * (4 / 3 * ρ') + ρ * ρ' ^ 2 := by
          grw [h_third, trace_add, trace_add, trace_add, norm_add_le, norm_add₃_le,
            h.norm_trace_rest_le, h'.norm_trace_rest_le,
            norm_trace_mul_le (norm_proj_mul_le hQ h.norm_sub_linear_le) (h'.norm_le hρ'),
            norm_trace_mul_le (norm_proj_mul_le hQ h.norm_linear_le) h'.norm_sub_linear_le]
      _ ≤ (ρ + ρ') ^ 3 := by
          nlinarith [mul_nonneg (sq_nonneg ρ) h'.nonneg, mul_nonneg h.nonneg (sq_nonneg ρ')]

/-- Let `Q` be an orthogonal projection and `Y = L + S + ⋯` an expansion in `ρ ≤ 1 / 3`. Then
`det (1 + Q Y)` is the exponential of `tr Q L + tr Q S - tr (Q L)² / 2 + r` with `‖r‖ ≤ 8 ρ³`. -/
lemma IsExpansion.exists_det_one_add_mul_eq_exp (hQ : IsStarProjection Q)
    (h : IsExpansion Q Y L S ρ) (hρ : ρ ≤ 1 / 3) :
    ∃ r : ℂ, (1 + Q * Y).det =
        cexp ((Q * L).trace + ((Q * S).trace - (Q * L * (Q * L)).trace / 2) + r) ∧
      ‖r‖ ≤ 8 * ρ ^ 3 := by
  have hQY : ‖Q * Y‖ ≤ 4 / 3 * ρ := norm_proj_mul_le hQ (h.norm_le hρ)
  have h_small : ‖Q * Y‖ ≤ 2⁻¹ := by linarith
  -- The rest has three parts: that of the logarithm, that of `tr Q Y`, and that of `tr (Q Y)²`.
  let rLog : ℂ := (logOneAdd (Q * Y)).trace - ((Q * Y).trace - (Q * Y * (Q * Y)).trace / 2)
  let rSquare : ℂ := (Q * (Y - L) * (Q * Y)).trace + (Q * L * (Q * (Y - L))).trace
  have h_square : (Q * Y * (Q * Y)).trace = (Q * L * (Q * L)).trace + rSquare := by
    simp only [rSquare, mul_sub, sub_mul, trace_sub]
    ring
  refine ⟨rLog + (Q * (Y - L - S)).trace - rSquare / 2, ?_, ?_⟩
  · rw [det_one_add_eq_exp_trace_logOneAdd h_small]
    congr 1
    simp only [rLog, h_square, mul_sub Q Y, mul_sub Q (Y - L) S, trace_sub]
    ring
  · have hQ_sub : ‖Q * (Y - L)‖ ≤ ρ ^ 2 := norm_proj_mul_le hQ h.norm_sub_linear_le
    have h_log : ‖rLog‖ ≤ 2 * (4 / 3 * ρ) ^ 3 :=
      (norm_trace_logOneAdd_sub_le h_small).trans (by gcongr)
    have h_rSquare : ‖rSquare‖ ≤ ρ ^ 2 * (4 / 3 * ρ) + ρ * ρ ^ 2 :=
      norm_add_le_of_le (norm_trace_mul_le hQ_sub hQY)
        (norm_trace_mul_le (norm_proj_mul_le hQ h.norm_linear_le) hQ_sub)
    calc ‖rLog + (Q * (Y - L - S)).trace - rSquare / 2‖
        ≤ 2 * (4 / 3 * ρ) ^ 3 + ρ ^ 3 + (ρ ^ 2 * (4 / 3 * ρ) + ρ * ρ ^ 2) / 2 := by
          grw [norm_sub_le, norm_add_le, norm_div, Complex.norm_ofNat, h_log,
            h.norm_trace_rest_le, h_rSquare]
      _ ≤ 8 * ρ ^ 3 := by nlinarith [pow_nonneg h.nonneg 3]

/-- The trace of `Q A (1 - Q) B`. For a projection `Q` it involves only the blocks of `A` and `B`
that cross `Q`, that is, that map the range of `Q` to its kernel or the kernel to the range. -/
def crossTrace (Q A B : Matrix n n ℂ) : ℂ := (Q * A * (1 - Q) * B).trace

/-- The crossing trace `tr Q A (1 - Q) B` is `tr Q A B - tr Q A Q B`. -/
lemma crossTrace_eq_trace_sub_trace (Q A B : Matrix n n ℂ) :
    crossTrace Q A B = (Q * (A * B)).trace - (Q * A * (Q * B)).trace := by
  simp [crossTrace, mul_sub, sub_mul, mul_assoc]

/-- The sum of the crossing traces `crossTrace Q Aᵢ Aⱼ = tr Q Aᵢ (1 - Q) Aⱼ` over `i ≤ j`, with the
terms `i = j` halved: `∑ᵢ tr Q Aᵢ (1 - Q) Aᵢ / 2 + ∑_{i < j} tr Q Aᵢ (1 - Q) Aⱼ`. -/
def crossTraceSum (Q A₁ A₂ A₃ : Matrix n n ℂ) : ℂ :=
  (crossTrace Q A₁ A₁ + crossTrace Q A₂ A₂ + crossTrace Q A₃ A₃) / 2 +
    crossTrace Q A₁ A₂ + crossTrace Q A₁ A₃ + crossTrace Q A₂ A₃

/-- The determinant `det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))`. For an orthogonal projection `Q` it
is the principal minor of `exp A₁ exp A₂ exp A₃` on the range of `Q`. -/
def expMinor (Q A₁ A₂ A₃ : Matrix n n ℂ) : ℂ :=
  (1 + Q * (NormedSpace.exp A₁ * NormedSpace.exp A₂ * NormedSpace.exp A₃ - 1)).det

/-- The terms of first and second order in `log (expMinor Q A₁ A₂ A₃)`, namely
`∑ᵢ tr Q Aᵢ + ∑ᵢ tr Q Aᵢ (1 - Q) Aᵢ / 2 + ∑_{i < j} tr Q Aᵢ (1 - Q) Aⱼ`. -/
def logMinorQuadratic (Q A₁ A₂ A₃ : Matrix n n ℂ) : ℂ :=
  (Q * (A₁ + A₂ + A₃)).trace + crossTraceSum Q A₁ A₂ A₃

/-- The principal logarithm of the quotient of the minor `expMinor Q A₁ A₂ A₃` by the exponential
of the main terms `logMinorQuadratic Q A₁ A₂ A₃`. For small `Aᵢ` it is the sum of the terms of order
three and more in `log (expMinor Q A₁ A₂ A₃)`. -/
def logMinorRemainder (Q A₁ A₂ A₃ : Matrix n n ℂ) : ℂ :=
  log (expMinor Q A₁ A₂ A₃ * cexp (-logMinorQuadratic Q A₁ A₂ A₃))

/-- Let `Q` be an orthogonal projection and let `A₁`, `A₂`, `A₃` have Frobenius norm at most
`ρ ≤ 1 / 10`. Then the minor `expMinor Q A₁ A₂ A₃ = det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` is the
exponential of `logMinorQuadratic Q A₁ A₂ A₃ + r` for some `r` with `‖r‖ ≤ 216 ρ³`. -/
lemma exists_expMinor_eq_cexp (hQ : IsStarProjection Q) (hρ : ρ ≤ 1 / 10)
    (h₁ : ‖A₁‖ ≤ ρ) (h₂ : ‖A₂‖ ≤ ρ) (h₃ : ‖A₃‖ ≤ ρ) :
    ∃ r : ℂ, expMinor Q A₁ A₂ A₃ = cexp (logMinorQuadratic Q A₁ A₂ A₃ + r) ∧
      ‖r‖ ≤ 216 * ρ ^ 3 := by
  have h_exp {A : Matrix n n ℂ} (hA : ‖A‖ ≤ ρ) :
      IsExpansion Q (NormedSpace.exp A - 1) A ((2 : ℂ)⁻¹ • (A * A)) ρ :=
    isExpansion_exp hQ hA (by linarith)
  have hρ_le_third : ρ ≤ 1 / 3 := by linarith
  let L : Matrix n n ℂ := A₁ + A₂ + A₃
  let S : Matrix n n ℂ :=
    (2 : ℂ)⁻¹ • (A₁ * A₁) + (2 : ℂ)⁻¹ • (A₂ * A₂) + A₁ * A₂ + (2 : ℂ)⁻¹ • (A₃ * A₃) + (A₁ + A₂) * A₃
  have h_product : IsExpansion Q
      (NormedSpace.exp A₁ * NormedSpace.exp A₂ * NormedSpace.exp A₃ - 1) L S (ρ + ρ + ρ) :=
    ((h_exp h₁).mul hQ (h_exp h₂) hρ_le_third hρ_le_third).mul hQ (h_exp h₃) (by linarith)
      hρ_le_third
  -- The square `tr (∑ Q Aᵢ)² / 2` is a sum over `i ≤ j`, as the trace is cyclic.
  have h_main : (Q * L).trace + ((Q * S).trace - (Q * L * (Q * L)).trace / 2) =
      logMinorQuadratic Q A₁ A₂ A₃ := by
    simp only [L, S, logMinorQuadratic, crossTraceSum, crossTrace_eq_trace_sub_trace, mul_add,
      add_mul, trace_add, mul_smul_comm, trace_smul, smul_eq_mul, trace_mul_comm (Q * A₂) (Q * A₁),
      trace_mul_comm (Q * A₃) (Q * A₁), trace_mul_comm (Q * A₃) (Q * A₂)]
    ring
  obtain ⟨r, h_det, hr⟩ := h_product.exists_det_one_add_mul_eq_exp hQ (by linarith)
  exact ⟨r, by rw [expMinor, h_det, h_main], hr.trans_eq (by ring)⟩

/-- Let `Q` be an orthogonal projection and let `A₁`, `A₂`, `A₃` have Frobenius norm at most
`ρ ≤ 1 / 10`. Then the minor `expMinor Q A₁ A₂ A₃ = det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` is the
exponential of the traces `logMinorQuadratic` of first and second order in the `Aᵢ` plus the rest
`logMinorRemainder`, the principal logarithm of the minor divided by `exp logMinorQuadratic`. -/
lemma expMinor_eq_cexp_logMinorQuadratic_add_logMinorRemainder (hQ : IsStarProjection Q)
    (hρ : ρ ≤ 1 / 10) (h₁ : ‖A₁‖ ≤ ρ) (h₂ : ‖A₂‖ ≤ ρ) (h₃ : ‖A₃‖ ≤ ρ) :
    expMinor Q A₁ A₂ A₃ = cexp (logMinorQuadratic Q A₁ A₂ A₃ + logMinorRemainder Q A₁ A₂ A₃) := by
  obtain ⟨r, h_minor, -⟩ := exists_expMinor_eq_cexp hQ hρ h₁ h₂ h₃
  have h_quotient : expMinor Q A₁ A₂ A₃ * cexp (-logMinorQuadratic Q A₁ A₂ A₃) = cexp r := by
    rw [h_minor, ← Complex.exp_add, add_neg_cancel_comm]
  rw [Complex.exp_add, logMinorRemainder, h_quotient, exp_log (exp_ne_zero r), h_minor,
    Complex.exp_add]

/-- Let `Q` be an orthogonal projection and let `A₁`, `A₂`, `A₃` have Frobenius norm at most
`ρ ≤ 1 / 10`. Then the rest `logMinorRemainder Q A₁ A₂ A₃`, the sum of the terms of order three and
more in `log det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))`, has norm at most `216 ρ³`. -/
lemma norm_logMinorRemainder_le_of_norm_le (hQ : IsStarProjection Q) (hρ : ρ ≤ 1 / 10)
    (h₁ : ‖A₁‖ ≤ ρ) (h₂ : ‖A₂‖ ≤ ρ) (h₃ : ‖A₃‖ ≤ ρ) :
    ‖logMinorRemainder Q A₁ A₂ A₃‖ ≤ 216 * ρ ^ 3 := by
  obtain ⟨r, h_minor, hr⟩ := exists_expMinor_eq_cexp hQ hρ h₁ h₂ h₃
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg A₁).trans h₁
  have hr_small : ‖r‖ ≤ 216 * (1 / 10) ^ 3 := hr.trans (by gcongr)
  -- As `r` is small, it is the principal logarithm of `exp r`.
  have h_im : |r.im| < Real.pi := by linarith [abs_im_le_norm r, Real.pi_gt_three]
  have h_rest : logMinorRemainder Q A₁ A₂ A₃ = r := by
    rw [logMinorRemainder, h_minor, ← Complex.exp_add, add_neg_cancel_comm,
      log_exp (neg_lt_of_abs_lt h_im) (lt_of_abs_lt h_im).le]
  rwa [h_rest]

/-- Let `Q` be an orthogonal projection and let `A₁`, `A₂`, `A₃` have Frobenius norm at most
`ρ ≤ 1 / 10`. Then the minor `expMinor Q A₁ A₂ A₃ = det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` divided
by the exponential of `logMinorQuadratic Q A₁ A₂ A₃ = ∑ᵢ tr Q Aᵢ + ∑'_{i ≤ j} tr Q Aᵢ (1 - Q) Aⱼ`
(the terms `i = j` halved) lies in the slit plane, away from the cut of the principal logarithm. -/
lemma expMinor_mul_mem_slitPlane (hQ : IsStarProjection Q) (hρ : ρ ≤ 1 / 10)
    (h₁ : ‖A₁‖ ≤ ρ) (h₂ : ‖A₂‖ ≤ ρ) (h₃ : ‖A₃‖ ≤ ρ) :
    expMinor Q A₁ A₂ A₃ * cexp (-logMinorQuadratic Q A₁ A₂ A₃) ∈ slitPlane := by
  obtain ⟨r, h_minor, hr⟩ := exists_expMinor_eq_cexp hQ hρ h₁ h₂ h₃
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg A₁).trans h₁
  have hr_small : ‖r‖ ≤ 216 * (1 / 10) ^ 3 := hr.trans (by gcongr)
  have h_near : ‖cexp r - 1‖ < 1 := by
    linarith [Complex.norm_exp_sub_one_le (x := r) (by linarith)]
  rw [h_minor, ← Complex.exp_add, add_neg_cancel_comm, ← add_sub_cancel 1 (cexp r)]
  exact mem_slitPlane_of_norm_lt_one h_near

/-- If `Q` is idempotent and commutes with `A`, then `1 + Q (exp A - 1) = exp (Q A)`. -/
lemma one_add_mul_exp_sub_one (hQ : IsIdempotentElem Q) (hA : Commute Q A) :
    1 + Q * (NormedSpace.exp A - 1) = NormedSpace.exp (Q * A) := by
  -- On the range of `Q` the matrix `Q A` acts as `A`, and on its kernel as `0`.
  have h_range : SemiconjBy Q (Q * A) A := by rw [SemiconjBy, ← mul_assoc, hQ.eq, hA.eq]
  have h_kernel : SemiconjBy (1 - Q) (Q * A) 0 := by
    rw [SemiconjBy, ← mul_assoc, hQ.one_sub_mul_self, zero_mul, zero_mul]
  have h_exp_range : Q * NormedSpace.exp (Q * A) = NormedSpace.exp A * Q := h_range.exp_right.eq
  have h_exp_kernel : (1 - Q) * NormedSpace.exp (Q * A) = NormedSpace.exp 0 * (1 - Q) :=
    h_kernel.exp_right.eq
  rw [NormedSpace.exp_zero] at h_exp_kernel
  linear_combination (norm := noncomm_ring) hA.exp_right.eq - h_exp_range - h_exp_kernel

/-- If `Q` is idempotent and commutes with `A₁`, `A₂`, `A₃`, then the rest
`logMinorRemainder Q A₁ A₂ A₃` vanishes. -/
lemma logMinorRemainder_eq_zero (hQ : IsIdempotentElem Q)
    (h₁ : Commute Q A₁) (h₂ : Commute Q A₂) (h₃ : Commute Q A₃) :
    logMinorRemainder Q A₁ A₂ A₃ = 0 := by
  -- The minor is `exp tr Q (A₁ + A₂ + A₃)`, and the terms of second order vanish.
  have h_mul {X Y : Matrix n n ℂ} (hX : Commute Q X) :
      1 + Q * (X * Y - 1) = (1 + Q * (X - 1)) * (1 + Q * (Y - 1)) := by
    linear_combination (norm := noncomm_ring)
      Q * hX.eq * (Y - 1) - hQ.eq * X * (Y - 1) + hQ.eq * (Y - 1)
  have h_minor : expMinor Q A₁ A₂ A₃ = cexp (Q * (A₁ + A₂ + A₃)).trace := by
    rw [expMinor, h_mul (h₁.exp_right.mul_right h₂.exp_right), h_mul h₁.exp_right,
      one_add_mul_exp_sub_one hQ h₁, one_add_mul_exp_sub_one hQ h₂, one_add_mul_exp_sub_one hQ h₃,
      det_mul, det_mul]
    simp only [det_exp, mul_add, trace_add, Complex.exp_add]
  have h_cross {A : Matrix n n ℂ} (hA : Commute Q A) (B : Matrix n n ℂ) : crossTrace Q A B = 0 := by
    rw [crossTrace, hA.eq, mul_assoc A, hQ.mul_one_sub_self, mul_zero, zero_mul, trace_zero]
  simp [logMinorRemainder, logMinorQuadratic, crossTraceSum, h_minor, h_cross h₁, h_cross h₂,
    h_cross h₃, ← Complex.exp_add]

/-- The rest `logMinorRemainder`, the logarithm of the quotient of
`det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` by the exponential of the traces `logMinorQuadratic` of
first and second order, does not change when the `Aᵢ` are conjugated by an involution `U` that
commutes with `Q`. -/
lemma logMinorRemainder_conj {U : Matrix n n ℂ} (hU : U * U = 1) (hUQ : Commute U Q) :
    logMinorRemainder Q (U * A₁ * U) (U * A₂ * U) (U * A₃ * U) = logMinorRemainder Q A₁ A₂ A₃ := by
  have hQ : U * Q * U = Q := by rw [hUQ.eq, mul_assoc, hU, mul_one]
  have h_mul (X Y : Matrix n n ℂ) : U * X * U * (U * Y * U) = U * (X * Y) * U := by
    linear_combination (norm := noncomm_ring) U * X * hU * Y * U
  have h_exp (X : Matrix n n ℂ) : NormedSpace.exp (U * X * U) = U * NormedSpace.exp X * U := by
    have h_semiconj : SemiconjBy U X (U * X * U) := by
      rw [SemiconjBy, mul_assoc (U * X), hU, mul_one]
    have h_exp_semiconj : U * NormedSpace.exp X = NormedSpace.exp (U * X * U) * U :=
      h_semiconj.exp_right.eq
    rw [h_exp_semiconj, mul_assoc _ U U, hU, mul_one]
  have h_det (X : Matrix n n ℂ) : (1 + Q * (U * X * U - 1)).det = (1 + Q * (X - 1)).det := by
    have h_conj : 1 + Q * (U * X * U - 1) = U * (1 + Q * (X - 1)) * U := by
      linear_combination (norm := noncomm_ring) hQ - hU - hUQ.eq * X * U
    rw [h_conj, det_mul_comm, ← mul_assoc, hU, one_mul]
  have h_trace (X : Matrix n n ℂ) : (Q * (U * X * U)).trace = (Q * X).trace := by
    rw [← mul_assoc, trace_mul_comm, ← mul_assoc, ← mul_assoc, hQ]
  have h_cross (X Y : Matrix n n ℂ) : crossTrace Q (U * X * U) (U * Y * U) = crossTrace Q X Y := by
    have h_conj : Q * (U * X * U) * (1 - Q) * (U * Y * U) = Q * (U * (X * (1 - Q) * Y) * U) := by
      linear_combination (norm := noncomm_ring) Q * U * X * (hU - hQ) * Y * U
    rw [crossTrace, h_conj, h_trace, crossTrace, mul_assoc Q, mul_assoc Q]
  -- Hence neither the minor nor its main terms change.
  simp only [logMinorRemainder, expMinor, logMinorQuadratic, crossTraceSum, h_exp, h_mul, h_det,
    h_cross, mul_add Q, trace_add, h_trace]

/-! ### Scaling the crossing parts -/

/-- The crossing part `Q A (1 - Q) + (1 - Q) A Q` of `A`: for a projection `Q`, the two off-diagonal
blocks of `A` with respect to the range and the kernel of `Q`. -/
def crossPart (Q A : Matrix n n ℂ) : Matrix n n ℂ := Q * A * (1 - Q) + (1 - Q) * A * Q

/-- The matrix `A` with its crossing part `Q A (1 - Q) + (1 - Q) A Q` multiplied by `τ`. -/
def scaleCross (Q A : Matrix n n ℂ) (τ : ℂ) : Matrix n n ℂ :=
  A - crossPart Q A + τ • crossPart Q A

lemma scaleCross_one : scaleCross Q A 1 = A := by simp [scaleCross]

/-- For an idempotent `Q`, the matrix `scaleCross Q A 0`, that is `A` without its crossing part
`Q A (1 - Q) + (1 - Q) A Q`, commutes with `Q`. -/
lemma commute_scaleCross_zero (hQ : IsIdempotentElem Q) : Commute Q (scaleCross Q A 0) := by
  have h_blocks : scaleCross Q A 0 = Q * A * Q + (1 - Q) * A * (1 - Q) := by
    rw [scaleCross, zero_smul, add_zero, crossPart]
    noncomm_ring
  rw [h_blocks]
  calc Q * (Q * A * Q + (1 - Q) * A * (1 - Q))
      = Q * A * Q := by simp [mul_add, ← mul_assoc, hQ.eq, hQ.mul_one_sub_self]
    _ = (Q * A * Q + (1 - Q) * A * (1 - Q)) * Q := by
        simp [add_mul, mul_assoc, hQ.eq, hQ.one_sub_mul_self]

/-- For an idempotent `Q`, conjugation by the involution `2 Q - 1` changes the sign of the factor
`τ` by which `scaleCross Q A τ` multiplies the crossing part `Q A (1 - Q) + (1 - Q) A Q` of the
matrix `A`. -/
lemma scaleCross_neg (hQ : IsIdempotentElem Q) (τ : ℂ) :
    scaleCross Q A (-τ) = (2 * Q - 1) * scaleCross Q A τ * (2 * Q - 1) := by
  -- The involution is `1` on the range of `Q` and `-1` on its kernel.
  have h_left : (2 * Q - 1) * Q = Q := by
    rw [sub_one_mul, mul_assoc, hQ.eq, two_mul, add_sub_cancel_right]
  have h_right : Q * (2 * Q - 1) = Q := by linear_combination (norm := noncomm_ring) 2 * hQ.eq
  have h_conj : (2 * Q - 1) * A * (2 * Q - 1) = A - 2 * crossPart Q A := by
    rw [crossPart]
    noncomm_ring
  have h_cross : (2 * Q - 1) * crossPart Q A * (2 * Q - 1) = -crossPart Q A := by
    calc (2 * Q - 1) * crossPart Q A * (2 * Q - 1)
        = (2 * Q - 1) * Q * A * (2 * Q - 1) + (2 * Q - 1) * A * (Q * (2 * Q - 1)) -
            2 * ((2 * Q - 1) * Q * A * (Q * (2 * Q - 1))) := by
          rw [crossPart]
          noncomm_ring
      _ = -crossPart Q A := by
          rw [h_left, h_right, crossPart]
          noncomm_ring
  rw [scaleCross, scaleCross, mul_add, add_mul, mul_sub _ A, sub_mul _ _ (2 * Q - 1),
    mul_smul_comm, smul_mul_assoc, h_conj, h_cross, neg_smul, smul_neg]
  noncomm_ring

/-- For an orthogonal projection `Q`, the crossing part `Q A (1 - Q) + (1 - Q) A Q` has the same
Frobenius norm as the commutator `⁅Q, A⁆`. -/
lemma norm_crossPart (hQ : IsStarProjection Q) : ‖crossPart Q A‖ = ‖⁅Q, A⁆‖ := by
  have h_eq : crossPart Q A = (2 * Q - 1) * ⁅Q, A⁆ := by
    rw [crossPart, Ring.lie_def]
    linear_combination (norm := noncomm_ring) -2 * hQ.isIdempotentElem.eq * A
  rw [h_eq, frobenius_norm_mul_of_unitary
    (Unitary.star_mul_self_of_mem hQ.two_mul_sub_one_mem_unitary)]

/-- For an orthogonal projection `Q`, removing from `A` its crossing part
`Q A (1 - Q) + (1 - Q) A Q` does not increase the Frobenius norm. -/
lemma norm_sub_crossPart_le (hQ : IsStarProjection Q) : ‖A - crossPart Q A‖ ≤ ‖A‖ := by
  -- The matrix is the mean of `A` and of its conjugate by the unitary matrix `2 Q - 1`.
  have h_unitary : 2 * Q - 1 ∈ unitary (Matrix n n ℂ) := hQ.two_mul_sub_one_mem_unitary
  have h_left {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
      ‖U * X‖ = ‖X‖ := frobenius_norm_mul_of_unitary (Unitary.star_mul_self_of_mem hU) X
  have h_conj : ‖(2 * Q - 1) * A * (2 * Q - 1)‖ = ‖A‖ := by
    rw [mul_assoc, h_left h_unitary, ← norm_star, star_mul, h_left (Unitary.star_mem h_unitary),
      norm_star]
  have h_mean : (2 : ℝ) • (A - crossPart Q A) = A + (2 * Q - 1) * A * (2 * Q - 1) := by
    rw [crossPart, two_smul]
    noncomm_ring
  have h_norm : 2 * ‖A - crossPart Q A‖ ≤ ‖A‖ + ‖A‖ := by
    grw [← norm_smul_of_nonneg zero_le_two, h_mean, norm_add_le, h_conj]
  linarith

/-- Let `Q` be an orthogonal projection, `‖A‖ ≤ δ` and `‖⁅Q, A⁆‖ ≤ ζ` (Frobenius norms). Multiplying
the crossing part `Q A (1 - Q) + (1 - Q) A Q` of `A` by `τ` with `‖τ‖ ζ ≤ δ` gives a matrix of norm
at most `2 δ`. -/
lemma norm_scaleCross_le (hQ : IsStarProjection Q) (hA : ‖A‖ ≤ δ) (hζ : ‖⁅Q, A⁆‖ ≤ ζ) {τ : ℂ}
    (hτ : ‖τ‖ * ζ ≤ δ) : ‖scaleCross Q A τ‖ ≤ 2 * δ :=
  calc ‖scaleCross Q A τ‖ ≤ ‖A‖ + ‖τ‖ * ‖⁅Q, A⁆‖ := by
        grw [scaleCross, norm_add_le, norm_smul, norm_sub_crossPart_le hQ, norm_crossPart hQ]
    _ ≤ 2 * δ := by grw [hA, hζ, hτ, two_mul]

lemma differentiable_matrix_det : Differentiable ℂ (det : Matrix n n ℂ → ℂ) := by
  -- The Leibniz formula makes it a polynomial in the entries.
  have h_entry (i j : n) : Differentiable ℂ fun X : Matrix n n ℂ ↦ X i j :=
    (entryLinearMap ℂ ℂ i j).toContinuousLinearMap.differentiable
  rw [funext (det_apply' (n := n) (R := ℂ))]
  fun_prop

/-- The minor `det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` is an entire function of the factor `τ` that
multiplies the crossing parts `Q Aᵢ (1 - Q) + (1 - Q) Aᵢ Q` of the `Aᵢ`. -/
lemma differentiable_expMinor_scaleCross :
    Differentiable ℂ fun τ : ℂ ↦
      expMinor Q (scaleCross Q A₁ τ) (scaleCross Q A₂ τ) (scaleCross Q A₃ τ) := by
  have h_exp : Differentiable ℂ (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) :=
    fun X ↦ (NormedSpace.exp_analytic X).differentiableAt
  have h_det : Differentiable ℂ (det : Matrix n n ℂ → ℂ) := differentiable_matrix_det
  unfold expMinor scaleCross
  fun_prop

/-- The sum `∑ᵢ tr Q Aᵢ + ∑'_{i ≤ j} tr Q Aᵢ (1 - Q) Aⱼ` (the terms `i = j` halved) is an entire
function of the factor `τ` that multiplies the crossing parts `Q Aᵢ (1 - Q) + (1 - Q) Aᵢ Q`. -/
lemma differentiable_logMinorQuadratic_scaleCross :
    Differentiable ℂ fun τ : ℂ ↦
      logMinorQuadratic Q (scaleCross Q A₁ τ) (scaleCross Q A₂ τ) (scaleCross Q A₃ τ) := by
  have h_trace : Differentiable ℂ (trace : Matrix n n ℂ → ℂ) :=
    (traceLinearMap n ℂ ℂ).toContinuousLinearMap.differentiable
  unfold logMinorQuadratic crossTraceSum crossTrace scaleCross
  fun_prop

/-- Schwarz's lemma for an even function: if `f` is holomorphic and bounded by `C` on the disc of
radius `R`, even, and zero at the origin, then `‖f z‖ ≤ C (‖z‖ / R) ^ 2` on the disc. -/
lemma norm_le_mul_sq_of_even {f : ℂ → ℂ} {R C : ℝ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (h_even : ∀ w : ℂ, f (-w) = f w)
    (h_zero : f 0 = 0) (h_bound : ∀ w ∈ Metric.ball (0 : ℂ) R, ‖f w‖ ≤ C)
    (hz : z ∈ Metric.ball (0 : ℂ) R) : ‖f z‖ ≤ C * (‖z‖ / R) ^ 2 := by
  have hR : 0 < R := Metric.nonempty_ball.1 ⟨z, hz⟩
  have h_deriv_zero : deriv f 0 = 0 := by
    simpa [h_even, self_eq_neg] using deriv_comp_neg f 0
  have h_order : (fun w : ℂ ↦ f w - f 0) =o[nhds 0] fun w : ℂ ↦ ‖w - 0‖ ^ 1 := by
    simpa [h_deriv_zero] using
      (hf.differentiableAt (Metric.ball_mem_nhds 0 hR)).hasDerivAt.isLittleO.norm_right
  simpa [h_zero] using dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (R₂ := C) hf
    (fun w hw ↦ by simpa [h_zero] using h_bound w hw) h_order hz

/-- For an idempotent `Q`, multiply the crossing parts `Q Aᵢ (1 - Q) + (1 - Q) Aᵢ Q` of the `Aᵢ` by
`τ`, which gives `Bᵢ = scaleCross Q Aᵢ τ`. Then the rest `logMinorRemainder Q B₁ B₂ B₃`, the
principal logarithm of the quotient of `det (1 + Q (exp B₁ exp B₂ exp B₃ - 1))` by the exponential
of the traces `logMinorQuadratic` of first and second order, is an even function of `τ`. -/
lemma logMinorRemainder_scaleCross_neg (hQ : IsIdempotentElem Q) (τ : ℂ) :
    logMinorRemainder Q (scaleCross Q A₁ (-τ)) (scaleCross Q A₂ (-τ)) (scaleCross Q A₃ (-τ)) =
      logMinorRemainder Q (scaleCross Q A₁ τ) (scaleCross Q A₂ τ) (scaleCross Q A₃ τ) := by
  have h_involution : (2 * Q - 1) * (2 * Q - 1) = 1 := by
    linear_combination (norm := noncomm_ring) 4 * hQ.eq
  have h_commute : Commute (2 * Q - 1) Q :=
    ((Commute.ofNat_left 2 Q).mul_left (.refl Q)).sub_left (.one_left Q)
  simpa only [scaleCross_neg hQ] using logMinorRemainder_conj h_involution h_commute

/-- Let `Q` be an orthogonal projection, `0 < ζ < δ ≤ 1 / 20`, and let `A₁`, `A₂`, `A₃` have
Frobenius norm at most `δ` and commutators with `Q` of Frobenius norm at most `ζ`. Then
`logMinorRemainder Q A₁ A₂ A₃`, the sum of the terms of order three and more in
`log det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))`, has norm at most `216 (2 δ)³ (ζ / δ)²`. -/
lemma norm_logMinorRemainder_le (hQ : IsStarProjection Q) (hδ : δ ≤ 1 / 20) (hζ : 0 < ζ)
    (hζδ : ζ < δ) (h₁ : ‖A₁‖ ≤ δ) (h₂ : ‖A₂‖ ≤ δ) (h₃ : ‖A₃‖ ≤ δ)
    (hζ₁ : ‖⁅Q, A₁⁆‖ ≤ ζ) (hζ₂ : ‖⁅Q, A₂⁆‖ ≤ ζ) (hζ₃ : ‖⁅Q, A₃⁆‖ ≤ ζ) :
    ‖logMinorRemainder Q A₁ A₂ A₃‖ ≤ 216 * (2 * δ) ^ 3 * (ζ / δ) ^ 2 := by
  -- Multiply the crossing parts by `τ` with `ζ ‖τ‖ < δ`. The rest `f τ` is holomorphic, bounded,
  -- even and zero at the origin, so Schwarz's lemma bounds `f 1`.
  let f (τ : ℂ) : ℂ := logMinorRemainder Q (scaleCross Q A₁ τ) (scaleCross Q A₂ τ)
    (scaleCross Q A₃ τ)
  have hQ_idem : IsIdempotentElem Q := hQ.isIdempotentElem
  have h_double : 2 * δ ≤ 1 / 10 := by linarith
  have h_norm {A : Matrix n n ℂ} (hA : ‖A‖ ≤ δ) (hζA : ‖⁅Q, A⁆‖ ≤ ζ) {τ : ℂ}
      (hτ : τ ∈ Metric.ball (0 : ℂ) (δ / ζ)) : ‖scaleCross Q A τ‖ ≤ 2 * δ :=
    norm_scaleCross_le hQ hA hζA ((lt_div_iff₀ hζ).1 (mem_ball_zero_iff.1 hτ)).le
  have h_holomorphic : DifferentiableOn ℂ f (Metric.ball 0 (δ / ζ)) :=
    (differentiable_expMinor_scaleCross.mul
      differentiable_logMinorQuadratic_scaleCross.neg.cexp).differentiableOn.clog fun τ hτ ↦
        expMinor_mul_mem_slitPlane hQ h_double
          (h_norm h₁ hζ₁ hτ) (h_norm h₂ hζ₂ hτ) (h_norm h₃ hζ₃ hτ)
  have h_bound (τ : ℂ) (hτ : τ ∈ Metric.ball (0 : ℂ) (δ / ζ)) : ‖f τ‖ ≤ 216 * (2 * δ) ^ 3 :=
    norm_logMinorRemainder_le_of_norm_le hQ h_double
      (h_norm h₁ hζ₁ hτ) (h_norm h₂ hζ₂ hτ) (h_norm h₃ hζ₃ hτ)
  have h_zero : f 0 = 0 :=
    logMinorRemainder_eq_zero hQ_idem (commute_scaleCross_zero hQ_idem)
      (commute_scaleCross_zero hQ_idem) (commute_scaleCross_zero hQ_idem)
  have h_even (τ : ℂ) : f (-τ) = f τ := logMinorRemainder_scaleCross_neg hQ_idem τ
  simpa [f, scaleCross_one] using norm_le_mul_sq_of_even h_holomorphic h_even h_zero h_bound
    (z := 1) (by simpa [one_lt_div hζ])

/-- Let `Q` be an orthogonal projection, `δ ≤ 1 / 20`, and let `A₁`, `A₂`, `A₃` have Frobenius norm
at most `δ` and commutators with `Q` of Frobenius norm at most `ζ`. Then
`det (1 + Q (exp A₁ exp A₂ exp A₃ - 1))` is the exponential of
`∑ᵢ tr Q Aᵢ + ∑'_{i ≤ j} tr Q Aᵢ (1 - Q) Aⱼ + r` with `‖r‖ ≤ 10⁴ δ ζ²`, where `∑'` halves the terms
`i = j`; the second sum is `crossTraceSum Q A₁ A₂ A₃`. -/
theorem exists_det_one_add_proj_mul_eq_exp (hQ : IsStarProjection Q) (hδ : δ ≤ 1 / 20)
    (h₁ : ‖A₁‖ ≤ δ) (h₂ : ‖A₂‖ ≤ δ) (h₃ : ‖A₃‖ ≤ δ)
    (hζ₁ : ‖⁅Q, A₁⁆‖ ≤ ζ) (hζ₂ : ‖⁅Q, A₂⁆‖ ≤ ζ) (hζ₃ : ‖⁅Q, A₃⁆‖ ≤ ζ) :
    ∃ r : ℂ, (1 + Q * (NormedSpace.exp A₁ * NormedSpace.exp A₂ * NormedSpace.exp A₃ - 1)).det =
        cexp ((Q * (A₁ + A₂ + A₃)).trace + crossTraceSum Q A₁ A₂ A₃ + r) ∧
      ‖r‖ ≤ 10 ^ 4 * δ * ζ ^ 2 := by
  have hδ_small : δ ≤ 1 / 10 := by linarith
  refine ⟨logMinorRemainder Q A₁ A₂ A₃, by simpa only [expMinor, logMinorQuadratic] using
    expMinor_eq_cexp_logMinorQuadratic_add_logMinorRemainder hQ hδ_small h₁ h₂ h₃, ?_⟩
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg A₁).trans h₁
  -- For `δ ≤ ζ` the bound of third order is enough, and for `ζ = 0` the `Aᵢ` commute with `Q`.
  rcases le_or_gt δ ζ with hδζ | hζδ
  · calc ‖logMinorRemainder Q A₁ A₂ A₃‖ ≤ 216 * δ * δ ^ 2 :=
          (norm_logMinorRemainder_le_of_norm_le hQ hδ_small h₁ h₂ h₃).trans_eq (by ring)
      _ ≤ 10 ^ 4 * δ * ζ ^ 2 := by
          gcongr
          norm_num
  rcases ((norm_nonneg ⁅Q, A₁⁆).trans hζ₁).eq_or_lt with rfl | hζ
  · simp [logMinorRemainder_eq_zero hQ.isIdempotentElem, commute_iff_lie_eq, norm_le_zero_iff.1 hζ₁,
      norm_le_zero_iff.1 hζ₂, norm_le_zero_iff.1 hζ₃]
  · calc ‖logMinorRemainder Q A₁ A₂ A₃‖ ≤ 216 * (2 * δ) ^ 3 * (ζ / δ) ^ 2 :=
          norm_logMinorRemainder_le hQ hδ hζ hζδ h₁ h₂ h₃ hζ₁ hζ₂ hζ₃
      _ = 1728 * δ * ζ ^ 2 := by
          field_simp [(hζ.trans hζδ).ne']
          norm_num
      _ ≤ 10 ^ 4 * δ * ζ ^ 2 := by nlinarith [mul_nonneg hδ_nonneg (sq_nonneg ζ)]

end New.DiscreteSeries

end
