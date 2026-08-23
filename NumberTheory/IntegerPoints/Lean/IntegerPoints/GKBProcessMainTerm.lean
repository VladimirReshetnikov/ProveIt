import IntegerPoints.GKBProcessBlock

/-!
# Graham--Kolesnik B-process: the stationary main term

This module bounds the closed stationary sum returned by Lemma 3.6 in terms
of the dyadic dual estimates proved in `GKBProcessBlock`.

There are two genuine endpoint issues.  If

`alpha = f'(b)` and `beta = f'(a)`,

then Lemma 3.6 sums over the closed integer interval
`Finset.Icc ceil(alpha) floor(beta)`, whereas an exponent-pair estimate uses
the natural half-open interval `intRange alpha beta = (alpha, beta]`.  Passing
to `intRange` can therefore delete the lower endpoint.  Moreover, the
identity between the literal stationary weight and `sqrt (-phi'')` is proved
only on the open derivative interval, so an integral upper endpoint must also
be isolated.  Comparing with the full dual-weight sum charges

* at most two literal stationary weights, and
* at most one dual weight at the upper endpoint.

The literal weights are bounded by `curvatureWeightBound`.  The possible dual
endpoint is put in a terminal interval based at
`max alpha (beta / 2)` and bounded by its `dualModelWeight`.

The remaining full dual `intRange` is decomposed exactly by
`sum_derivative_intRange_eq_sum_truncatedDyadicBlocks`.  Each nonempty block
is then bounded by `norm_weighted_dual_block_le`; blocks whose left endpoint
has already passed `beta` are empty.  Thus the final theorem exposes a finite
sum of explicit block models together with the three endpoint costs, ready
for the real-power normalization in `GKBProcessArithmetic`.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## The two stationary summands -/

/-- The stationary summand in the form obtained after applying the Legendre
phase identity, but still carrying the literal curvature weight of `f`. -/
noncomputable def stationarySummand
    (f x phi : ℝ → ℝ) (nu : ℝ) : ℂ :=
  ((stationaryWeight f x nu : ℝ) : ℂ) * e (-phi nu - 1 / 8)

/-- The summand suitable for Abel summation and an exponent-pair estimate. -/
noncomputable def dualSummand (phi : ℝ → ℝ) (nu : ℝ) : ℂ :=
  ((dualWeight phi nu : ℝ) : ℂ) * e (-phi nu - 1 / 8)

@[simp]
theorem norm_stationarySummand (f x phi : ℝ → ℝ) (nu : ℝ) :
    ‖stationarySummand f x phi nu‖ = stationaryWeight f x nu := by
  unfold stationarySummand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold stationaryWeight; positivity), norm_e, mul_one]

@[simp]
theorem norm_dualSummand (phi : ℝ → ℝ) (nu : ℝ) :
    ‖dualSummand phi nu‖ = dualWeight phi nu := by
  unfold dualSummand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold dualWeight; exact Real.sqrt_nonneg _), norm_e, mul_one]

/-- A literal term of the Lemma 3.6 stationary sum is exactly
`stationarySummand` once the Legendre value identity is substituted. -/
theorem lemma36_stationaryTerm_eq_stationarySummand
    {f x phi : ℝ → ℝ} {nu : ℝ}
    (hlegendre : phi nu = nu * x nu - f (x nu)) :
    e (f (x nu) - nu * x nu - 1 / 8) /
        ((Real.sqrt |iteratedDeriv 2 f (x nu)| : ℝ) : ℂ) =
      stationarySummand f x phi nu := by
  rw [stationary_phase_eq_neg_legendre hlegendre]
  unfold stationarySummand stationaryWeight
  push_cast
  ring

/-- The two summands agree away from both derivative endpoints. -/
theorem stationarySummand_eq_dualSummand_of_mem_ne
    {N s y eps a b : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    {nu : ℝ} (hnu : nu ∈ Icc (deriv f b) (deriv f a))
    (hnu_left : nu ≠ deriv f b) (hnu_right : nu ≠ deriv f a) :
    stationarySummand f x phi nu = dualSummand phi nu := by
  unfold stationarySummand dualSummand
  rw [stationaryWeight_eq_dualWeight_of_mem_ne
    hN hs hy hP heps heps_half hf hab hx hlegendre
      hnu hnu_left hnu_right]

/-! ## Natural casts in the two range conventions -/

/-- A natural in `closedRange A B` casts into the real closed interval. -/
theorem natCast_mem_Icc_of_mem_closedRange {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) {n : ℕ}
    (hn : n ∈ closedRange A B) : (n : ℝ) ∈ Icc A B := by
  have hB : 0 ≤ B := hA.trans hAB
  rw [closedRange, Finset.mem_Icc] at hn
  constructor
  · exact (Nat.le_ceil A).trans (by exact_mod_cast hn.1)
  · have hnFloor : (n : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hn.2
    exact hnFloor.trans (Nat.floor_le hB)

/-- A natural in `intRange A B` casts into `(A,B]`. -/
theorem natCast_mem_Ioc_of_mem_intRange {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ}
    (hn : n ∈ intRange A B) : (n : ℝ) ∈ Ioc A B := by
  rw [intRange, Finset.mem_Ioc] at hn
  exact ⟨(Nat.floor_lt hA).mp hn.1, (Nat.le_floor_iff hB).mp hn.2⟩

/-! ## A generic two-endpoint replacement inequality -/

/--
Replace a summand on a closed natural range by another summand on the
half-open range.  The two functions need agree except possibly where the
natural index casts exactly to the upper real endpoint.

The cost is two copies of `Rclosed` (the possible deleted lower endpoint and
the possible literal upper endpoint) and one copy of `Rupper` (the possible
replacement summand at the upper endpoint).  No integrality case split is
exposed to callers.
-/
theorem norm_sum_closedRange_le_norm_sum_intRange_add_endpoints
    {A B Rclosed Rupper : ℝ} (g h : ℕ → ℂ)
    (hRclosed : 0 ≤ Rclosed) (hRupper : 0 ≤ Rupper)
    (hg : ∀ n ∈ closedRange A B, ‖g n‖ ≤ Rclosed)
    (heq : ∀ n ∈ intRange A B, (n : ℝ) ≠ B → g n = h n)
    (hh : ∀ n ∈ intRange A B, (n : ℝ) = B → ‖h n‖ ≤ Rupper) :
    ‖∑ n ∈ closedRange A B, g n‖ ≤
      ‖∑ n ∈ intRange A B, h n‖ + 2 * Rclosed + Rupper := by
  classical
  let E : Finset ℕ := (intRange A B).filter fun n => (n : ℝ) = B
  have hEsub : E ⊆ intRange A B := Finset.filter_subset _ _
  have hEcard : E.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm n hn
    simp only [E, Finset.mem_filter] at hm hn
    exact_mod_cast hm.2.trans hn.2.symm
  have hsumSupport :
      ∑ n ∈ intRange A B, (g n - h n) = ∑ n ∈ E, (g n - h n) := by
    symm
    apply Finset.sum_subset hEsub
    intro n hn hnE
    have hne : (n : ℝ) ≠ B := by
      intro hnB
      exact hnE (by simpa only [E, Finset.mem_filter] using ⟨hn, hnB⟩)
    rw [heq n hn hne, sub_self]
  have herror :
      ‖(∑ n ∈ intRange A B, g n) - ∑ n ∈ intRange A B, h n‖ ≤
        Rclosed + Rupper := by
    rw [← Finset.sum_sub_distrib, hsumSupport]
    calc
      ‖∑ n ∈ E, (g n - h n)‖ ≤
          ∑ n ∈ E, ‖g n - h n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ E, (Rclosed + Rupper) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hgn : ‖g n‖ ≤ Rclosed :=
          hg n (intRange_subset_closedRange A B hn'.1)
        have hhn : ‖h n‖ ≤ Rupper := hh n hn'.1 hn'.2
        exact (norm_sub_le (g n) (h n)).trans (add_le_add hgn hhn)
      _ = (E.card : ℝ) * (Rclosed + Rupper) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (Rclosed + Rupper) := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg hRclosed hRupper)
        exact_mod_cast hEcard
      _ = Rclosed + Rupper := one_mul _
  have hreplace :
      ‖∑ n ∈ intRange A B, g n‖ ≤
        ‖∑ n ∈ intRange A B, h n‖ + (Rclosed + Rupper) := by
    calc
      ‖∑ n ∈ intRange A B, g n‖ =
          ‖((∑ n ∈ intRange A B, g n) - ∑ n ∈ intRange A B, h n) +
            ∑ n ∈ intRange A B, h n‖ := by
        congr 1
        ring
      _ ≤ ‖(∑ n ∈ intRange A B, g n) - ∑ n ∈ intRange A B, h n‖ +
          ‖∑ n ∈ intRange A B, h n‖ := norm_add_le _ _
      _ ≤ (Rclosed + Rupper) + ‖∑ n ∈ intRange A B, h n‖ :=
        add_le_add herror le_rfl
      _ = ‖∑ n ∈ intRange A B, h n‖ + (Rclosed + Rupper) := by ring
  have hclosed := norm_sum_closedRange_le_norm_sum_intRange_add
    A B Rclosed g hRclosed hg
  calc
    ‖∑ n ∈ closedRange A B, g n‖ ≤
        ‖∑ n ∈ intRange A B, g n‖ + Rclosed := hclosed
    _ ≤ (‖∑ n ∈ intRange A B, h n‖ + (Rclosed + Rupper)) +
          Rclosed := add_le_add hreplace le_rfl
    _ = ‖∑ n ∈ intRange A B, h n‖ + 2 * Rclosed + Rupper := by ring

/-! ## The literal closed stationary sum -/

/-- Cast the literal closed integer sum from Lemma 3.6 to the corresponding
closed natural sum and substitute the Legendre phase identity exactly. -/
theorem lemma36_stationarySum_eq_stationary_closedRange
    {a b : ℝ} {f x phi : ℝ → ℝ}
    (hAlpha : 0 ≤ deriv f b) (hAlphaBeta : deriv f b ≤ deriv f a)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    (∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)) =
      ∑ n ∈ closedRange (deriv f b) (deriv f a),
        stationarySummand f x phi n := by
  rw [sum_integer_Icc_eq_sum_closedRange hAlpha hAlphaBeta]
  apply Finset.sum_congr rfl
  intro n hn
  apply lemma36_stationaryTerm_eq_stationarySummand
  exact hlegendre n
    (natCast_mem_Icc_of_mem_closedRange hAlpha hAlphaBeta hn)

/-- The closed literal stationary sum is bounded by the full dual-weight
`intRange`, two literal endpoint weights, and one possible dual upper-endpoint
weight.  The latter is left as an arbitrary bound for reuse. -/
theorem norm_stationary_closedRange_le_dual_intRange_add_endpoints
    {N s y eps a b Rupper : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : 0 < eps) (heps_quarter : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    (hupper : dualWeight phi (deriv f a) ≤ Rupper) :
    ‖∑ n ∈ closedRange (deriv f b) (deriv f a),
        stationarySummand f x phi n‖ ≤
      ‖∑ n ∈ intRange (deriv f b) (deriv f a), dualSummand phi n‖ +
        2 * curvatureWeightBound N s y + Rupper := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps_quarter hf
  have hAlpha : 0 ≤ deriv f b := hends.2.2.1.le
  have hBeta : 0 ≤ deriv f a := hAlpha.trans hends.2.2.2.1
  have hRclosed : 0 ≤ curvatureWeightBound N s y :=
    (curvatureWeightBound_pos hN hs hy).le
  have hdual_nonneg : 0 ≤ dualWeight phi (deriv f a) := by
    unfold dualWeight
    exact Real.sqrt_nonneg _
  have hRupper : 0 ≤ Rupper := hdual_nonneg.trans hupper
  apply norm_sum_closedRange_le_norm_sum_intRange_add_endpoints
    (fun n : ℕ => stationarySummand f x phi (n : ℝ))
    (fun n : ℕ => dualSummand phi (n : ℝ))
    hRclosed hRupper
  · intro n hn
    rw [norm_stationarySummand]
    exact stationaryWeight_le_curvatureWeightBound
      hN hs hy hP heps_quarter hf hx
        (natCast_mem_Icc_of_mem_closedRange hAlpha hends.2.2.2.1 hn)
  · intro n hn hnBeta
    have hnIoc := natCast_mem_Ioc_of_mem_intRange hAlpha hBeta hn
    apply stationarySummand_eq_dualSummand_of_mem_ne
      hN hs hy (by omega) heps (heps_quarter.trans_lt (by norm_num))
      hf hab hx hlegendre
    · exact ⟨hnIoc.1.le, hnIoc.2⟩
    · exact hnIoc.1.ne'
    · exact hnBeta
  · intro n _ hnBeta
    rw [norm_dualSummand, hnBeta]
    exact hupper

/-- Literal Lemma 3.6 form of the preceding endpoint comparison. -/
theorem norm_lemma36_stationarySum_le_dual_intRange_add_endpoints
    {N s y eps a b Rupper : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : 0 < eps) (heps_quarter : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    (hupper : dualWeight phi (deriv f a) ≤ Rupper) :
    ‖∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ intRange (deriv f b) (deriv f a), dualSummand phi n‖ +
        2 * curvatureWeightBound N s y + Rupper := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps_quarter hf
  rw [lemma36_stationarySum_eq_stationary_closedRange
    hends.2.2.1.le hends.2.2.2.1 hlegendre]
  exact norm_stationary_closedRange_le_dual_intRange_add_endpoints
    hN hs hy hP heps heps_quarter hf hab hx hlegendre hupper

/-! ## Explicit block and endpoint models -/

/-- The explicit upper bound supplied by the input exponent pair and Abel
summation on the `j`-th dyadic frequency block. -/
noncomputable def dualBlockUpperBound
    {k l s : ℝ} (params : Parameters k l s) (y alpha : ℝ) (j : ℕ) : ℝ :=
  let J := dyadicCut alpha j
  params.pairConstant *
      (((y ^ (1 / s) * J ^ (-(1 / s))) ^ k * J ^ l) +
        (y ^ (1 / s))⁻¹ * J ^ (1 / s)) *
    dualModelWeight (1 / s) (y ^ (1 / s)) J

theorem dualBlockUpperBound_nonneg
    {k l s y alpha : ℝ} (params : Parameters k l s)
    (hs : 0 < s) (hy : 0 < y) (hAlpha : 0 < alpha) (j : ℕ) :
    0 ≤ dualBlockUpperBound params y alpha j := by
  unfold dualBlockUpperBound
  have hJ : 0 < dyadicCut alpha j := dyadicCut_pos hAlpha j
  have heta : 0 < y ^ (1 / s) := Real.rpow_pos_of_pos hy _
  have hsigma : 0 < 1 / s := by positivity
  have hweight : 0 ≤ dualModelWeight (1 / s) (y ^ (1 / s))
      (dyadicCut alpha j) := Real.sqrt_nonneg _
  apply mul_nonneg
  · apply mul_nonneg params.pairConstant_nonneg
    positivity
  · exact hweight

/-- A terminal dyadic base whose doubled interval always contains `B`. -/
noncomputable def terminalScale (A B : ℝ) : ℝ := max A (B / 2)

theorem terminalScale_spec {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    0 < terminalScale A B ∧ A ≤ terminalScale A B ∧
      terminalScale A B ≤ B ∧ B ≤ 2 * terminalScale A B := by
  have hB : 0 < B := hA.trans_le hAB
  unfold terminalScale
  refine ⟨hA.trans_le (le_max_left _ _), le_max_left _ _, ?_, ?_⟩
  · exact max_le hAB (by linarith)
  · have := le_max_right A (B / 2)
    linarith

/-- The possible dual upper-endpoint term is bounded by a model at the
terminal scale `max alpha (beta/2)`. -/
theorem dualWeight_deriv_left_le_terminalModel
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    dualWeight phi (deriv f a) ≤
      dualModelWeight (1 / s) (y ^ (1 / s))
        (terminalScale (deriv f b) (deriv f a)) := by
  have hends := endpoint_derivative_bounds hN hs hy
    params.four_le_originalOrder params.originalError_le_quarter hf
  let J : ℝ := terminalScale (deriv f b) (deriv f a)
  have hJspec := terminalScale_spec hends.2.2.1 hends.2.2.2.1
  have hraw := params.lemma39Class N y a b f x phi hN hy hf hab hphi hx
    hlegendre J hJspec.2.1 hJspec.2.2.1
  have hmax : max (deriv f b) J = J := max_eq_right hJspec.2.1
  have hmin : min (deriv f a) (2 * J) = deriv f a :=
    min_eq_left hJspec.2.2.2
  have hmem : deriv f a ∈
      Icc (max (deriv f b) J) (min (deriv f a) (2 * J)) := by
    rw [hmax, hmin]
    exact ⟨hJspec.2.2.1, le_rfl⟩
  have hP3 : 3 ≤ params.originalOrder :=
    (by omega : 3 ≤ 4).trans params.four_le_originalOrder
  exact dualWeight_le_dualModelWeight hJspec.1 (by positivity)
    (Real.rpow_pos_of_pos hy _) hP3
    params.lemma39Error_le_quarter hraw hmem

/-! ## One truncated block and the full dyadic sum -/

/-- Every truncated dyadic block is bounded by its explicit block model.
If its left endpoint has passed the derivative interval, the block is empty;
otherwise the stored Lemma 3.9 class and exponent-pair estimate feed directly
into `norm_weighted_dual_block_le`. -/
theorem norm_dual_truncatedDyadicBlock_le
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    (j : ℕ) :
    ‖∑ n ∈ truncatedDyadicBlock (deriv f a) (deriv f b) j,
        dualSummand phi n‖ ≤
      dualBlockUpperBound params y (deriv f b) j := by
  have hends := endpoint_derivative_bounds hN hs hy
    params.four_le_originalOrder params.originalError_le_quarter hf
  let J : ℝ := dyadicCut (deriv f b) j
  have hJ : 0 < J := dyadicCut_pos hends.2.2.1 j
  have hAlphaJ : deriv f b ≤ J := by
    rw [← dyadicCut_zero (deriv f b)]
    exact dyadicCut_monotone hends.2.2.1.le (Nat.zero_le j)
  by_cases hJBeta : J ≤ deriv f a
  · have hraw := params.lemma39Class N y a b f x phi hN hy hf hab hphi hx
      hlegendre J hAlphaJ hJBeta
    have hP3 : 3 ≤ params.originalOrder :=
      (by omega : 3 ≤ 4).trans params.four_le_originalOrder
    have hblock := norm_weighted_dual_block_le hJ (by positivity)
      (Real.rpow_pos_of_pos hy _) hP3
      params.lemma39Error_le_quarter hraw
      params.pairOrder_le_originalOrder params.lemma39Error_le_pairError
      params.pairConstant_nonneg
      (fun u v huv => params.pairBound J (y ^ (1 / s)) u v phi
        hJ (Real.rpow_pos_of_pos hy _) huv)
    simpa only [dualSummand, truncatedDyadicBlock, dualBlockUpperBound,
      J, max_eq_right hAlphaJ, dyadicCut_succ] using hblock
  · have hBetaJ : deriv f a ≤ J := le_of_not_ge hJBeta
    have hempty :
        truncatedDyadicBlock (deriv f a) (deriv f b) j = ∅ := by
      unfold truncatedDyadicBlock intRange
      apply Finset.Ioc_eq_empty_of_le
      apply Nat.floor_mono
      exact (min_le_left _ _).trans hBetaJ
    rw [hempty, Finset.sum_empty, norm_zero]
    exact dualBlockUpperBound_nonneg params hs hy hends.2.2.1 j

/-- Sum all fixedly many truncated blocks and apply the one-block estimate to
each of them. -/
theorem norm_dual_intRange_le_sum_dualBlockUpperBounds
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    ‖∑ n ∈ intRange (deriv f b) (deriv f a), dualSummand phi n‖ ≤
      ∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j := by
  rw [sum_derivative_intRange_eq_sum_truncatedDyadicBlocks
    (fun n : ℕ => dualSummand phi (n : ℝ))
      hN hs hy params.four_le_originalOrder
      params.originalError_le_quarter hf]
  calc
    ‖∑ j ∈ Finset.range (dyadicDepth s),
        ∑ n ∈ truncatedDyadicBlock (deriv f a) (deriv f b) j,
          dualSummand phi n‖ ≤
      ∑ j ∈ Finset.range (dyadicDepth s),
        ‖∑ n ∈ truncatedDyadicBlock (deriv f a) (deriv f b) j,
          dualSummand phi n‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j := by
      exact Finset.sum_le_sum fun j _ =>
        norm_dual_truncatedDyadicBlock_le
          params hN hs hy hf hab hphi hx hlegendre j

/-! ## Combined stationary-main-term estimate -/

/-- The complete reusable main-term bound: the literal closed stationary sum
from Lemma 3.6 is bounded by the finite collection of explicit dyadic block
models, two possible literal stationary endpoint terms, and the possible dual
upper-endpoint term. -/
theorem norm_lemma36_stationarySum_le_dyadicBlockUpperBounds
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    ‖∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)‖ ≤
      (∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j) +
        2 * curvatureWeightBound N s y +
          dualModelWeight (1 / s) (y ^ (1 / s))
            (terminalScale (deriv f b) (deriv f a)) := by
  have hterminal := dualWeight_deriv_left_le_terminalModel
    params hN hs hy hf hab hphi hx hlegendre
  have hbridge := norm_lemma36_stationarySum_le_dual_intRange_add_endpoints
    hN hs hy params.four_le_originalOrder params.originalError_pos
      params.originalError_le_quarter hf hab hx hlegendre hterminal
  have hblocks := norm_dual_intRange_le_sum_dualBlockUpperBounds
    params hN hs hy hf hab hphi hx hlegendre
  exact hbridge.trans (add_le_add (add_le_add hblocks le_rfl) le_rfl)

end GKB

end LeanProofs.IntegerPoints
