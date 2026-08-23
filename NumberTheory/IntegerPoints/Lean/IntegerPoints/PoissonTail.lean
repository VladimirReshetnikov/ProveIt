import IntegerPoints.PoissonIntegrals

/-!
# Truncated Poisson summation: the tail bound

For `f ∈ C²` on `[a, b]` with `f'` decreasing and `H₁ < f' < H₂`, half-integers
`a ≤ p ≤ q ≤ b`, and `N ≥ max(−H₁, H₂)`,
`‖∑_{h ∈ T} ∫_p^q e(f(x) − hx) dx‖ ≤ 4/π + (2/π) log(H₂ − H₁ + 1)`
where `T = [−N, H₁ − 1] ∪ [H₂ + 1, N]`.  Each integral is integrated by parts once
(`PS.parts_phase`); the boundary terms `e(f(q) − hq)/(2πi(f'(q) − h))` have
`e(−hq) = (−1)^h`, so their sum over `T` is a pair of alternating series, bounded by `1/π`
in total at each endpoint; the remaining integrals are bounded by
`(1/2π) ∫_p^q (−f'') (2/(1 + H₂ − f') + 2/(1 + f' − H₁)) ≤ (2/π) log(H₂ − H₁ + 1)`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace PS

theorem tail_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : ℝ} (hab : a < b)
    (hanti : AntitoneOn (deriv f) (Set.Icc a b)) {H₁ H₂ : ℤ}
    (hH : ∀ x ∈ Set.Icc a b, (H₁ : ℝ) < deriv f x ∧ deriv f x < H₂)
    {p q : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) {mp mq : ℤ}
    (hp : p = mp + 1 / 2) (hq : q = mq + 1 / 2) {N : ℕ} (h1 : -(N : ℤ) ≤ H₁) (h2 : H₂ ≤ N) :
    ‖∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
        ∫ x in p..q, e (f x - h * x)‖ ≤ 4 / π + (2 / π) * Real.log ((H₂ : ℝ) - H₁ + 1) := by
  set T := Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N with hT
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hf'c : Continuous (deriv f) := hf1.continuous
  have hf''c : Continuous (deriv (deriv f)) := hf1.continuous_deriv le_rfl
  have hfd : ∀ x, HasDerivAt f (deriv f x) x :=
    fun x => ((hf.differentiable (by norm_num)) x).hasDerivAt
  have hf'd : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    fun x => ((hf1.differentiable one_ne_zero) x).hasDerivAt
  have hsub : Set.Icc p q ⊆ Set.Icc a b := Set.Icc_subset_Icc hap hqb
  have hf'' : ∀ x ∈ Set.Icc p q, deriv (deriv f) x ≤ 0 :=
    fun x hx => deriv2_nonpos hf hab hanti x (hsub hx)
  have hTmem : ∀ h ∈ T, h ≤ H₁ - 1 ∨ H₂ + 1 ≤ h := by
    intro h hh
    rw [hT, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hh
    omega
  have hne : ∀ h ∈ T, ∀ x ∈ Set.Icc p q, deriv f x - h ≠ 0 := by
    intro h hh x hx
    obtain ⟨hx1, hx2⟩ := hH x (hsub hx)
    rcases hTmem h hh with h' | h'
    · have : (h : ℝ) ≤ H₁ - 1 := by exact_mod_cast h'
      linarith
    · have : (H₂ : ℝ) + 1 ≤ h := by exact_mod_cast h'
      linarith
  -- integration by parts for each `h`
  have hparts : ∀ h ∈ T, ∫ x in p..q, e (f x - h * x) =
      e (f q - h * q) * ((1 / (deriv f q - h) : ℝ) : ℂ) / (2 * π * Complex.I) -
        e (f p - h * p) * ((1 / (deriv f p - h) : ℝ) : ℂ) / (2 * π * Complex.I) +
        (1 / (2 * π * Complex.I)) *
          ∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ) := by
    intro h hh
    have hφ : ∀ x, HasDerivAt (fun x => f x - h * x) (deriv f x - h) x := by
      intro x
      have := (hfd x).sub ((hasDerivAt_id x).const_mul (h : ℝ))
      refine this.congr_deriv ?_
      simp
    exact parts_phase (φ := fun x => f x - h * x) (φ' := fun x => deriv f x - h)
      (φ'' := deriv (deriv f)) hφ (fun x => (hf'd x).sub_const _) (hf'c.sub continuous_const)
      hf''c hpq (hne h hh)
  rw [Finset.sum_congr rfl hparts, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- the boundary sums
  have hbdry : ∀ (r : ℝ) (mr : ℤ), r = mr + 1 / 2 → r ∈ Set.Icc a b →
      ‖∑ h ∈ T, e (f r - h * r) * ((1 / (deriv f r - h) : ℝ) : ℂ) / (2 * π * Complex.I)‖ ≤
        1 / π := by
    intro r mr hr hrab
    obtain ⟨hc1, hc2⟩ := hH r hrab
    have hterm : ∀ h : ℤ, e (f r - h * r) * ((1 / (deriv f r - h) : ℝ) : ℂ) / (2 * π * Complex.I) =
        (e (f r) / (2 * π * Complex.I)) * ((((-1 : ℝ) ^ h / (deriv f r - h)) : ℝ) : ℂ) := by
      intro h
      rw [show f r - h * r = f r + -(h * ((mr : ℝ) + 1 / 2)) by rw [hr]; ring, KL.e_add,
        e_int_mul_half]
      push_cast
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, norm_mul, norm_div, norm_e_one, ← Complex.ofReal_sum,
      Complex.norm_real, Real.norm_eq_abs, norm_two_pi_I]
    have := abs_boundary_sum_le h1 h2 hc1 hc2
    calc 1 / (2 * π) * |∑ h ∈ T, (-1 : ℝ) ^ h / (deriv f r - h)| ≤ 1 / (2 * π) * 2 := by
          gcongr
      _ = 1 / π := by first | (field_simp; done) | (field_simp; ring)
  have hbq := hbdry q mq hq ⟨hap.trans hpq, hqb⟩
  have hbp := hbdry p mp hp ⟨hap, hpq.trans hqb⟩
  -- the integral sums
  set M : ℝ := (H₂ : ℝ) - H₁ + 1 with hM
  have hJ : ‖(1 / (2 * π * Complex.I)) * ∑ h ∈ T,
      ∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖ ≤
        (2 / π) * Real.log M := by
    rw [norm_mul, norm_div, norm_one, norm_two_pi_I]
    have hJh : ∀ h ∈ T,
        ‖∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖ ≤
          ∫ x in p..q, |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2) := by
      intro h hh
      refine (intervalIntegral.norm_integral_le_integral_norm hpq).trans (le_of_eq ?_)
      apply integral_congr
      intro x hx
      rw [Set.uIcc_of_le hpq] at hx
      simp only
      have hx0 : (0 : ℝ) < (deriv f x - h) ^ 2 := by
        have := hne h hh x hx
        positivity
      rw [norm_mul, norm_e_one, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos hx0]
      ring
    have hint : ∀ h ∈ T, IntervalIntegrable
        (fun x => |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2)) volume p q := by
      intro h hh
      apply ContinuousOn.intervalIntegrable_of_Icc hpq
      apply ContinuousOn.mul hf''c.abs.continuousOn
      apply ContinuousOn.div continuousOn_const ((hf'c.sub continuous_const).pow 2).continuousOn
      intro x hx
      exact pow_ne_zero 2 (hne h hh x hx)
    have hcontsum : ContinuousOn (fun x => ∑ h ∈ T, |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2))
        (Set.Icc p q) := by
      apply continuousOn_finset_sum
      intro h hh
      apply ContinuousOn.mul hf''c.abs.continuousOn
      apply ContinuousOn.div continuousOn_const ((hf'c.sub continuous_const).pow 2).continuousOn
      intro x hx
      exact pow_ne_zero 2 (hne h hh x hx)
    -- the comparison function
    have hA : ∀ x ∈ Set.Icc p q, 0 < 1 + ((H₂ : ℝ) - deriv f x) := fun x hx => by
      linarith [(hH x (hsub hx)).2]
    have hB : ∀ x ∈ Set.Icc p q, 0 < 1 + (deriv f x - H₁) := fun x hx => by
      linarith [(hH x (hsub hx)).1]
    have hcontR : ContinuousOn (fun x => (-deriv (deriv f) x) *
        (2 / (1 + ((H₂ : ℝ) - deriv f x)) + 2 / (1 + (deriv f x - H₁)))) (Set.Icc p q) := by
      apply ContinuousOn.mul hf''c.neg.continuousOn
      apply ContinuousOn.add
      · exact ContinuousOn.div continuousOn_const
          (continuous_const.add (continuous_const.sub hf'c)).continuousOn
          (fun x hx => (hA x hx).ne')
      · exact ContinuousOn.div continuousOn_const
          (continuous_const.add (hf'c.sub continuous_const)).continuousOn
          (fun x hx => (hB x hx).ne')
    have hpt : ∀ x ∈ Set.Icc p q,
        ∑ h ∈ T, |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2) ≤
          (-deriv (deriv f) x) * (2 / (1 + ((H₂ : ℝ) - deriv f x)) + 2 / (1 + (deriv f x - H₁))) := by
      intro x hx
      obtain ⟨hc1, hc2⟩ := hH x (hsub hx)
      rw [← Finset.mul_sum, abs_of_nonpos (hf'' x hx)]
      apply mul_le_mul_of_nonneg_left _ (by linarith [hf'' x hx])
      exact sum_inv_sq_tail_le h1 h2 hc1 hc2
    -- the two logarithmic integrals
    have hL1 : ∫ x in p..q, (-deriv (deriv f) x) / (1 + ((H₂ : ℝ) - deriv f x)) =
        Real.log (1 + ((H₂ : ℝ) - deriv f q)) - Real.log (1 + ((H₂ : ℝ) - deriv f p)) := by
      apply integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [Set.uIcc_of_le hpq] at hx
        have := (((hf'd x).const_sub (H₂ : ℝ)).const_add 1).log (hA x hx).ne'
        refine this.congr_deriv ?_
        ring
      · apply ContinuousOn.intervalIntegrable_of_Icc hpq
        exact ContinuousOn.div hf''c.neg.continuousOn
          (continuous_const.add (continuous_const.sub hf'c)).continuousOn
          (fun x hx => (hA x hx).ne')
    have hL2 : ∫ x in p..q, (-deriv (deriv f) x) / (1 + (deriv f x - H₁)) =
        Real.log (1 + (deriv f p - H₁)) - Real.log (1 + (deriv f q - H₁)) := by
      have := integral_eq_sub_of_hasDerivAt (a := p) (b := q)
        (f := fun x => -Real.log (1 + (deriv f x - H₁)))
        (f' := fun x => (-deriv (deriv f) x) / (1 + (deriv f x - H₁)))
        (by
          intro x hx
          rw [Set.uIcc_of_le hpq] at hx
          have := ((((hf'd x).sub_const (H₁ : ℝ)).const_add 1).log (hB x hx).ne').neg
          refine this.congr_deriv ?_
          ring)
        (by
          apply ContinuousOn.intervalIntegrable_of_Icc hpq
          exact ContinuousOn.div hf''c.neg.continuousOn
            (continuous_const.add (hf'c.sub continuous_const)).continuousOn
            (fun x hx => (hB x hx).ne'))
      rw [this]
      ring
    have hlog1 : Real.log (1 + ((H₂ : ℝ) - deriv f q)) - Real.log (1 + ((H₂ : ℝ) - deriv f p)) ≤
        Real.log M := by
      obtain ⟨hq1, hq2⟩ := hH q ⟨hap.trans hpq, hqb⟩
      obtain ⟨hp1, hp2⟩ := hH p ⟨hap, hpq.trans hqb⟩
      have e1 : Real.log (1 + ((H₂ : ℝ) - deriv f q)) ≤ Real.log M :=
        Real.log_le_log (by linarith) (by rw [hM]; linarith)
      have e2 : 0 ≤ Real.log (1 + ((H₂ : ℝ) - deriv f p)) := Real.log_nonneg (by linarith)
      linarith
    have hlog2 : Real.log (1 + (deriv f p - H₁)) - Real.log (1 + (deriv f q - H₁)) ≤
        Real.log M := by
      obtain ⟨hq1, hq2⟩ := hH q ⟨hap.trans hpq, hqb⟩
      obtain ⟨hp1, hp2⟩ := hH p ⟨hap, hpq.trans hqb⟩
      have e1 : Real.log (1 + (deriv f p - H₁)) ≤ Real.log M :=
        Real.log_le_log (by linarith) (by rw [hM]; linarith)
      have e2 : 0 ≤ Real.log (1 + (deriv f q - H₁)) := Real.log_nonneg (by linarith)
      linarith
    have hR : ∫ x in p..q, (-deriv (deriv f) x) *
        (2 / (1 + ((H₂ : ℝ) - deriv f x)) + 2 / (1 + (deriv f x - H₁))) ≤ 4 * Real.log M := by
      have heq : ∫ x in p..q, (-deriv (deriv f) x) *
          (2 / (1 + ((H₂ : ℝ) - deriv f x)) + 2 / (1 + (deriv f x - H₁))) =
          2 * (∫ x in p..q, (-deriv (deriv f) x) / (1 + ((H₂ : ℝ) - deriv f x))) +
            2 * ∫ x in p..q, (-deriv (deriv f) x) / (1 + (deriv f x - H₁)) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add]
        · apply integral_congr
          intro x _
          simp only
          ring
        · apply ContinuousOn.intervalIntegrable_of_Icc hpq
          exact continuousOn_const.mul (ContinuousOn.div hf''c.neg.continuousOn
            (continuous_const.add (continuous_const.sub hf'c)).continuousOn
            (fun x hx => (hA x hx).ne'))
        · apply ContinuousOn.intervalIntegrable_of_Icc hpq
          exact continuousOn_const.mul (ContinuousOn.div hf''c.neg.continuousOn
            (continuous_const.add (hf'c.sub continuous_const)).continuousOn
            (fun x hx => (hB x hx).ne'))
      rw [heq, hL1, hL2]
      linarith
    calc 1 / (2 * π) * ‖∑ h ∈ T,
          ∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖
        ≤ 1 / (2 * π) * ∑ h ∈ T,
            ‖∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖ := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ 1 / (2 * π) * ∑ h ∈ T, ∫ x in p..q, |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2) := by
          gcongr with h hh
          exact hJh h hh
      _ = 1 / (2 * π) * ∫ x in p..q, ∑ h ∈ T, |deriv (deriv f) x| * (1 / (deriv f x - h) ^ 2) := by
          rw [integral_finset_sum hint]
      _ ≤ 1 / (2 * π) * ∫ x in p..q, (-deriv (deriv f) x) *
            (2 / (1 + ((H₂ : ℝ) - deriv f x)) + 2 / (1 + (deriv f x - H₁))) := by
          gcongr
          exact integral_mono_on hpq (hcontsum.intervalIntegrable_of_Icc hpq)
            (hcontR.intervalIntegrable_of_Icc hpq) hpt
      _ ≤ 1 / (2 * π) * (4 * Real.log M) := by gcongr
      _ = (2 / π) * Real.log M := by field_simp; ring
  calc ‖(∑ h ∈ T, e (f q - h * q) * ((1 / (deriv f q - h) : ℝ) : ℂ) / (2 * π * Complex.I)) -
          (∑ h ∈ T, e (f p - h * p) * ((1 / (deriv f p - h) : ℝ) : ℂ) / (2 * π * Complex.I)) +
          (1 / (2 * π * Complex.I)) * ∑ h ∈ T,
            ∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖
      ≤ ‖(∑ h ∈ T, e (f q - h * q) * ((1 / (deriv f q - h) : ℝ) : ℂ) / (2 * π * Complex.I)) -
          (∑ h ∈ T, e (f p - h * p) * ((1 / (deriv f p - h) : ℝ) : ℂ) / (2 * π * Complex.I))‖ +
          ‖(1 / (2 * π * Complex.I)) * ∑ h ∈ T,
            ∫ x in p..q, e (f x - h * x) * ((deriv (deriv f) x / (deriv f x - h) ^ 2 : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ h ∈ T, e (f q - h * q) * ((1 / (deriv f q - h) : ℝ) : ℂ) / (2 * π * Complex.I)‖ +
          ‖∑ h ∈ T, e (f p - h * p) * ((1 / (deriv f p - h) : ℝ) : ℂ) / (2 * π * Complex.I)‖) +
          (2 / π) * Real.log M := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (1 / π + 1 / π) + (2 / π) * Real.log M := by gcongr
    _ ≤ 4 / π + (2 / π) * Real.log M := by
        have h4 : (1 : ℝ) / π + 1 / π ≤ 4 / π := by
          rw [← add_div]
          apply div_le_div_of_nonneg_right _ hpi.le
          norm_num
        linarith

end PS

end LeanProofs.IntegerPoints
