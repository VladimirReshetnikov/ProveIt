import Lib.General.LinearAlgebra.MatricesNearIdentity

/-!
# One minor of a product of three exponentials, to second order

For an orthogonal projection `P`, compress a product of three exponentials to its range.
Its determinant is the exponential of a linear term, an ordered sum of crossing traces,
and a remainder bounded by `10 ^ 4 * δ * ζ ^ 2`. Here `δ` bounds the Frobenius norms of
the three generators, and `ζ` bounds their commutators with `P`.

Each exponential traces one segment of the path to the product, starting with the
rightmost generator. Write `U = 1 + P (g - 1) P` and `V = (1 - P) g P` for the two
blocks. Jacobi's formula writes the logarithmic derivative of the compressed determinant
as the trace of `P A P + P A (1 - P) V U⁻¹`. Integrating its linear approximation on a
segment halves the self-crossing term and retains each earlier segment's contribution in
product order. The estimates on the two blocks give a dimension-independent error.

See `New.Appendix.DiscreteSeries.Periods` for related work.
-/

noncomputable section

open Matrix Norms.Frobenius Complex intervalIntegral

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {P X Y A : Matrix n n ℂ}

/-- If `X` and `Y` are within `ρ` and `σ` of the identity in the Frobenius norm, then their product
is within `ρ σ + ρ + σ` of it. -/
lemma norm_mul_sub_one_le {ρ σ : ℝ} (hX : ‖X - 1‖ ≤ ρ) (hY : ‖Y - 1‖ ≤ σ) :
    ‖X * Y - 1‖ ≤ ρ * σ + ρ + σ := by
  rw [show X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) by noncomm_ring]
  exact norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hX hY) hX) hY

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

/-- The trace of `Q A (1 - Q) B`. For a projection `Q` it involves only the blocks of `A` and `B`
that cross `Q`, that is, that map the range of `Q` to its kernel or the kernel to the range. -/
def crossTrace (Q A B : Matrix n n ℂ) : ℂ := (Q * A * (1 - Q) * B).trace

/-- The sum of the crossing traces `crossTrace Q Aᵢ Aⱼ = tr Q Aᵢ (1 - Q) Aⱼ` over `i ≤ j`, with the
terms `i = j` halved: `∑ᵢ tr Q Aᵢ (1 - Q) Aᵢ / 2 + ∑_{i < j} tr Q Aᵢ (1 - Q) Aⱼ`. -/
def crossTraceSum (Q A₁ A₂ A₃ : Matrix n n ℂ) : ℂ :=
  (crossTrace Q A₁ A₁ + crossTrace Q A₂ A₂ + crossTrace Q A₃ A₃) / 2 +
    crossTrace Q A₁ A₂ + crossTrace Q A₁ A₃ + crossTrace Q A₂ A₃

namespace MinorSecondOrder

local notation "Mat" => Matrix n n ℂ

/-- The diagonal block on the range of `P`, extended by the identity on its complement. -/
private def upper (P X : Mat) := 1 + P * (X - 1) * P
/-- The block mapping the range of `P` to its orthogonal complement. -/
private def lower (P X : Mat) := (1 - P) * X * P
/-- A single segment prepends an exponential to the earlier product `Y`. -/
private def seg (A Y : Mat) (t : ℝ) := NormedSpace.exp (t • A) * Y

private lemma seg_deriv (A Y : Mat) (s : ℝ) :
    HasDerivAt (seg A Y) (A * seg A Y s) s := by
  simpa [seg, mul_assoc] using! (hasDerivAt_exp_smul_const' A s).mul_const Y

private lemma upper_deriv (hP : IsIdempotentElem P) (A Y : Mat) (t : ℝ) :
    HasDerivAt (fun s ↦ upper P (seg A Y s))
      (P * A * P * upper P (seg A Y t) + P * A * (1 - P) * lower P (seg A Y t)) t := by
  refine ((((seg_deriv A Y t).sub_const 1).const_mul P).mul_const P).const_add 1 |>.congr_deriv ?_
  dsimp [upper, lower]
  generalize seg A Y t = X
  have hp := hP.eq
  noncomm_ring [hp]
  simp only [← Matrix.mul_assoc P P, hp]
  abel

private lemma lower_deriv (hP : IsIdempotentElem P) (A Y : Mat) (t : ℝ) :
    HasDerivAt (fun s ↦ lower P (seg A Y s))
      ((1 - P) * A * P * upper P (seg A Y t) + (1 - P) * A * (1 - P) * lower P (seg A Y t)) t := by
  refine (((seg_deriv A Y t).const_mul (1 - P)).mul_const P).congr_deriv ?_
  dsimp [upper, lower]
  generalize seg A Y t = X
  have hp := hP.eq
  noncomm_ring [hp]
  simp only [← Matrix.mul_assoc P P, hp]
  abel

/-- Integrating factor for a scalar equation on a single segment. -/
private lemma scalar_ode {f q : ℝ → ℂ}
    (hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (q t * f t) t)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousAt q t) (hm : Measurable q) :
    f 1 = f 0 * cexp (∫ t : ℝ in 0..1, q t) := by
  let F (t : ℝ) := ∫ s in 0..t, q s
  have hi (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt F (q t) t :=
    integral_hasDerivAt_right ((show ContinuousOn q (Set.uIcc 0 1) from
      fun s hs ↦ (hc s (by simpa using hs)).continuousWithinAt).mono
      (Set.uIcc_subset_uIcc_left (by simpa using ht))).intervalIntegrable
      ⟨Set.univ, Filter.univ_mem, hm.aestronglyMeasurable.restrict⟩ (hc t ht)
  have hz (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s ↦ f s * cexp (-F s)) 0 (Set.Icc 0 1) t :=
    ((hder t ht).fun_mul (hi t ht).neg.cexp).hasDerivWithinAt.congr_deriv (by ring)
  have hv := eq_of_norm_sub_le_zero (norm_image_sub_le_of_norm_deriv_le_segment_01' hz (by simp))
  simpa [F, Complex.exp_neg, ← div_eq_mul_inv, div_eq_iff (Complex.exp_ne_zero _)] using hv

/-- Integrating the block derivative gives the self-crossing and earlier crossings. -/
private lemma segmentDet {P A Y L : Mat} {δ ζ : ℝ} (hP : IsStarProjection P)
    (hB : ‖P * A * (1 - P)‖ ≤ ζ)
    (hnear : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖upper P (seg A Y t) - 1‖ < 1)
    (herror : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖lower P (seg A Y t) * (upper P (seg A Y t))⁻¹ -
        (L + t • ((1 - P) * A * P))‖ ≤ 153 * δ * ζ) :
    ∃ r : ℂ, (upper P (NormedSpace.exp A * Y)).det =
      (upper P Y).det * cexp ((P * A).trace + (P * A * (1 - P) * L).trace +
        (P * A * (1 - P) * ((1 - P) * A * P)).trace / 2 + r) ∧ ‖r‖ ≤ 153 * δ * ζ ^ 2 := by
  let U (t : ℝ) := upper P (seg A Y t)
  let V (t : ℝ) := lower P (seg A Y t)
  let B := P * A * (1 - P)
  let C := (1 - P) * A * P
  let H := P * A * P
  let q (t : ℝ) := (H + B * (V t * (U t)⁻¹)).trace
  let l (t : ℝ) := (H + B * (L + t • C)).trace
  have hU : Continuous U := continuous_iff_continuousAt.2 fun t ↦
    (upper_deriv hP.isIdempotentElem A Y t).continuousAt
  have hV : Continuous V := continuous_iff_continuousAt.2 fun t ↦
    (lower_deriv hP.isIdempotentElem A Y t).continuousAt
  have hu (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (U t).det ≠ 0 := by
    simpa using det_one_add_ne_zero (hnear t ht)
  have hq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContinuousAt q t := by
    simp only [q, Matrix.inv_def, Ring.inverse_eq_inv']
    fun_prop (disch := exact hu t ht)
  have hm : Measurable q := by
    simp only [q, Matrix.inv_def, Ring.inverse_eq_inv']
    fun_prop
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ (U s).det) (q t * (U t).det) t := by
    refine (New.hasDerivAt_det_of_isUnit (upper_deriv hP.isIdempotentElem A Y t)
      (isUnit_iff_ne_zero.2 (hu t ht))).congr_deriv ?_
    change ((H * U t + B * V t) * (U t)⁻¹).trace * (U t).det = _
    simp [q, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hu t ht))]
  have hmain : ∫ t : ℝ in 0..1, l t = (P * A).trace + (B * L).trace + (B * C).trace / 2 := by
    have htr : H.trace = (P * A).trace := by
      dsimp only [H]
      rw [trace_mul_comm _ P, ← mul_assoc, hP.isIdempotentElem.eq]
    simp_rw [l, Matrix.mul_add, mul_smul_comm, trace_add, trace_smul, real_smul, ← add_assoc]
    rw [intervalIntegral.integral_add intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    simp [htr, div_eq_inv_mul]
  have qi : IntervalIntegrable q MeasureTheory.volume 0 1 := (show ContinuousOn q (Set.uIcc 0 1) from
    fun t ht ↦ (hq t (by simpa using ht)).continuousWithinAt).intervalIntegrable
  have li : IntervalIntegrable l MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by unfold l; fun_prop) _ _
  -- Integrate the residual logarithmic derivative to obtain the error in the exponent.
  refine ⟨∫ t : ℝ in 0..1, q t - l t, ?_, ?_⟩
  · have h := scalar_ode hd hq hm
    rw [intervalIntegral.integral_sub qi li, hmain]
    simpa [U, seg, B, C] using h
  · calc
      _ ≤ ζ * (153 * δ * ζ) * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ by
        rw [Set.uIoc_of_le zero_le_one] at ht
        have hh := norm_trace_mul_le hB (herror t ⟨ht.1.le, ht.2⟩)
        simpa [q, l, B, C, U, V, Matrix.mul_sub, trace_sub, trace_add] using hh
      _ = _ := by norm_num; ring
/-- Start a segment at a product of at most two small exponentials. The first-order
off-diagonal increment is the corresponding block of its generator. -/
private lemma segment_estimates {P : Mat} (hP : IsStarProjection P) {A Y L : Mat} {δ ζ : ℝ} {k : ℕ}
    (hk : k ≤ 2) (hδ : δ ≤ 1 / 20) (hA : ‖A‖ ≤ δ) (hζ : ‖⁅P,A⁆‖ ≤ ζ)
    (hY : ‖Y - 1‖ ≤ (3 * (k : ℝ)) * δ) (hV : ‖lower P Y‖ ≤ (2 * (k : ℝ)) * ζ)
    (hL : ‖lower P Y - L‖ ≤ (15 * (k : ℝ)) * δ * ζ)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ‖seg A Y t - 1‖ ≤ (3 * ((k : ℝ) + 1)) * δ ∧
    ‖lower P (seg A Y t)‖ ≤ (2 * ((k : ℝ) + 1)) * ζ ∧
    ‖lower P (seg A Y t) - (L + t • ((1 - P) * A * P))‖ ≤ (15 * ((k : ℝ) + 1)) * δ * ζ ∧
    ‖lower P (seg A Y t) * (upper P (seg A Y t))⁻¹ - (L + t • ((1 - P) * A * P))‖ ≤
      153 * δ * ζ := by
  let C := (1 - P) * A * P
  let D := (1 - P) * A * (1 - P)
  let U s := upper P (seg A Y s)
  let V s := lower P (seg A Y s)
  let W (s : ℝ) := V s - (lower P Y + s • C)
  have hδ₀ := (norm_nonneg _).trans hA
  have hζ₀ := (norm_nonneg _).trans hζ
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hC : ‖C‖ ≤ ζ := by
    have hcomm : ⁅1 - P, A⁆ = -⁅P, A⁆ := by simp only [Ring.lie_def]; noncomm_ring
    exact (by simpa only [C, sub_sub_cancel, hcomm, norm_neg] using norm_cross_le (A := A) hP.one_sub : ‖C‖ ≤ ‖⁅P,A⁆‖).trans hζ
  have hD : ‖D‖ ≤ δ := norm_mul_proj_le hP.one_sub (norm_proj_mul_le hP.one_sub hA)
  have hg s (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖seg A Y s - 1‖ ≤ 3 * (k + 1 : ℝ) * δ := by
    have ha := norm_smul_le_of_le_one s hA hs
    have he := (norm_exp_sub_one_le (ha.trans (by linarith))).trans (mul_le_mul_of_nonneg_left ha (by norm_num))
    have hmul := norm_mul_sub_one_le he hY
    refine hmul.trans ?_
    have hky : 3 * (k : ℝ) * δ ≤ 6 * δ := by gcongr; linarith
    nlinarith [mul_le_mul_of_nonneg_left hky (show 0 ≤ 2 * δ by positivity),
      mul_nonneg hδ₀ (show 0 ≤ 1 - 12 * δ by linarith)]
  have hU s (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖U s - 1‖ ≤ 9 * δ := by
    have h := norm_mul_proj_le hP (norm_proj_mul_le hP (hg s hs))
    simpa only [U, upper, add_sub_cancel_left] using h.trans (show 3 * ((k : ℝ) + 1) * δ ≤ 9 * δ by
      gcongr; linarith)
  have wr s : HasDerivAt W (C * (U s - 1) + D * V s) s := by
    have hw := (lower_deriv hP.isIdempotentElem A Y s).sub
      (((hasDerivAt_id s).smul_const C).const_add (lower P Y))
    simpa only [W, C, D, U, V, id_eq, one_smul, mul_sub, mul_one, add_sub_right_comm, Pi.sub_apply] using! hw
  have w0 : W 0 = 0 := by simp [W, V, seg]
  have wbound s (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      ‖C * (U s - 1) + D * V s‖ ≤ 14 * δ * ζ + δ * ‖W s‖ := by
    have hv : ‖V s‖ ≤ ‖W s‖ + 5 * ζ := by
      calc ‖V s‖ = ‖W s + (lower P Y + s • C)‖ := by simp [W]
           _ ≤ ‖W s‖ + (2 * k * ζ + ζ) :=
             norm_add_le_of_le le_rfl (norm_add_le_of_le hV (norm_smul_le_of_le_one s hC hs))
           _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk' hζ₀]
    calc ‖C * (U s - 1) + D * V s‖ ≤ ζ * (9 * δ) + δ * (‖W s‖ + 5 * ζ) :=
           norm_add_le_of_le (norm_mul_le_of_le hC (hU s hs)) (norm_mul_le_of_le hD hv)
         _ = _ := by ring
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1))
    (show ContinuousOn (fun s ↦ ‖W s‖) (Set.Icc (0 : ℝ) 1) from
      fun s _ ↦ (wr s).continuousAt.norm.continuousWithinAt)
  -- Bound the maximum of the first-order error by its derivative over the unit interval.
  have hmx : ‖W x‖ ≤ 14 * δ * ζ + δ * ‖W x‖ := by
    have hb := norm_image_sub_le_of_norm_deriv_le_segment' (C := 14 * δ * ζ + δ * ‖W x‖)
      (fun s _ ↦ (wr s).hasDerivWithinAt)
      (fun s hs ↦ (wbound s ⟨hs.1, hs.2.le⟩).trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (isMaxOn_iff.mp hmax s ⟨hs.1, hs.2.le⟩) hδ₀) _)) x hx
    rw [w0, sub_zero, sub_zero] at hb
    exact hb.trans (mul_le_of_le_one_right (by positivity) hx.2)
  have hw : ‖W t‖ ≤ 15 * δ * ζ := (isMaxOn_iff.mp hmax t ht).trans (by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 20 - δ by linarith) (norm_nonneg (W x)), mul_nonneg hδ₀ hζ₀])
  have hl : ‖V t - (L + t • C)‖ ≤ 15 * (k + 1 : ℝ) * δ * ζ := by
    calc ‖V t - (L + t • C)‖ = ‖W t + (lower P Y - L)‖ := by congr 1; dsimp [W]; abel
         _ ≤ 15 * δ * ζ + 15 * k * δ * ζ := norm_add_le_of_le hw hL
         _ = _ := by ring
  have hv : ‖V t‖ ≤ 2 * (k + 1 : ℝ) * ζ := by
    calc ‖V t‖ = ‖W t + (lower P Y + t • C)‖ := by simp [W]
         _ ≤ 15 * δ * ζ + (2 * k * ζ + ζ) :=
           norm_add_le_of_le hw (norm_add_le_of_le hV (norm_smul_le_of_le_one t hC ht))
         _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 1 - 15 * δ by linarith) hζ₀]
  refine ⟨hg t ht, hv, hl, ?_⟩
  have hu : ‖U t - 1‖ ≤ 2⁻¹ := (hU t ht).trans (by linarith)
  have hi : ‖(U t)⁻¹ - 1‖ ≤ 18 * δ := by
    simpa only [add_sub_cancel] using (norm_inv_one_add_sub_one_le hu).trans
      (show 2 * ‖U t - 1‖ ≤ 18 * δ by linarith [hU t ht])
  change ‖V t * (U t)⁻¹ - (L + t • C)‖ ≤ _
  rw [show V t * (U t)⁻¹ - (L + t • C) = V t * ((U t)⁻¹ - 1) + (V t - (L + t • C)) by noncomm_ring]
  refine (norm_add_le_of_le (norm_mul_le_of_le (hv.trans (show 2 * ((k : ℝ) + 1) * ζ ≤ 6 * ζ by
    gcongr; linarith)) hi) (hl.trans (show 15 * ((k : ℝ) + 1) * δ * ζ ≤ 45 * δ * ζ by
    gcongr; linarith))).trans (by ring_nf; rfl)

/-- Estimates and determinant expansion after `k` segments. -/
private structure State (P Y L : Mat) (q : ℂ) (k : ℕ) (δ ζ : ℝ) : Prop where
  near : ‖Y - 1‖ ≤ 3 * (k : ℝ) * δ
  lower_le : ‖lower P Y‖ ≤ 2 * (k : ℝ) * ζ
  rest_le : ‖lower P Y - L‖ ≤ 15 * (k : ℝ) * δ * ζ
  det_eq : ∃ r : ℂ, (upper P Y).det = cexp (q + r) ∧ ‖r‖ ≤ 153 * (k : ℝ) * δ * ζ ^ 2

private lemma State.prepend {P A Y L : Mat} {q : ℂ} {k : ℕ} {δ ζ : ℝ} (h : State P Y L q k δ ζ)
    (hp : IsStarProjection P) (hk : k ≤ 2) (hδ : δ ≤ 1 / 20) (hA : ‖A‖ ≤ δ) (hζ : ‖⁅P,A⁆‖ ≤ ζ) :
    State P (NormedSpace.exp A * Y) (L + (1 - P) * A * P)
      (q + (P * A).trace + (P * A * (1 - P) * L).trace + (P * A * (1 - P) * ((1 - P) * A * P)).trace / 2) (k + 1) δ ζ := by
  have hb {t : ℝ} (ht : t ∈ Set.Icc 0 1) :=
    segment_estimates hp hk hδ hA hζ h.near h.lower_le h.rest_le ht
  obtain ⟨h1, h2, h3, -⟩ := hb (t := 1) (by simp)
  have hs (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖upper P (seg A Y t) - 1‖ < 1 := by
    have hx := norm_mul_proj_le hp (norm_proj_mul_le hp (hb ht).1)
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have hd := (norm_nonneg A).trans hA
    simp only [upper, add_sub_cancel_left]
    exact hx.trans_lt (by nlinarith [mul_nonneg (sub_nonneg.mpr hk') hd])
  obtain ⟨r, hr, hrn⟩ := segmentDet hp ((norm_cross_le hp).trans hζ) hs (fun t ht ↦ (hb ht).2.2.2)
  obtain ⟨r₀, h₀, h₀n⟩ := h.det_eq
  refine ⟨by simpa [seg] using h1, by simpa [seg] using h2, by simpa [seg] using h3, r₀ + r, ?_, ?_⟩
  · rw [hr, h₀, ← Complex.exp_add]
    congr 1
    ring
  · calc ‖r₀ + r‖ ≤ _ := norm_add_le_of_le h₀n hrn
         _ = _ := by push_cast; ring

private lemma trace_cross_blocks {P : Mat} (hp : IsIdempotentElem P) (A B : Mat) :
    (P * A * (1 - P) * ((1 - P) * B * P)).trace = crossTrace P A B := by
  have he : P * A * (1 - P) * ((1 - P) * B * P) = P * A * (1 - P) * B * P := by
    noncomm_ring [hp.eq]
    simp only [← Matrix.mul_assoc P P, hp.eq]
    abel
  rw [he, trace_mul_comm _ P]
  simp only [crossTrace, ← mul_assoc, hp.eq]

end MinorSecondOrder

open MinorSecondOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {Q A₁ A₂ A₃ : Matrix n n ℂ} {δ ζ : ℝ}

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
  have h₀ : State Q 1 0 0 0 δ ζ := by
    constructor <;> simp [upper, lower, sub_mul, hQ.isIdempotentElem.eq]
  -- Each new generator multiplies on the left.
  have third := h₀.prepend hQ (by decide) hδ h₃ hζ₃
  have second := third.prepend hQ (by decide) hδ h₂ hζ₂
  obtain ⟨r, he, hr⟩ := (second.prepend hQ (by decide) hδ h₁ hζ₁).det_eq
  refine ⟨r, ?_, ?_⟩
  · simp only [Matrix.mul_one, zero_add, mul_zero, trace_zero, add_zero, mul_add, trace_add,
      trace_cross_blocks hQ.isIdempotentElem, ← mul_assoc (NormedSpace.exp A₁)] at he
    rw [upper, det_one_add_mul_comm _ Q, ← mul_assoc, hQ.isIdempotentElem.eq] at he
    rw [he, crossTraceSum, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add]
    congr 1
    ring
  · have hd := (norm_nonneg A₁).trans h₁
    norm_num at hr ⊢
    nlinarith [mul_nonneg hd (sq_nonneg ζ)]

end New.DiscreteSeries

end
