import IntegerPoints.PoissonBounds
import IntegerPoints.GKLemma31

/-!
# Truncated Poisson summation: the analytic estimates

The three estimates behind Graham–Kolesnik Lemma 3.5:

* **The Euler–Maclaurin error.** `∫_p^q |ψ + S_N| ≤ (⌊q⌋ − ⌊p⌋ + 1)(9 + 8 log N)/N`, so the
  term `∫ (ψ + S_N)(e∘f)'` of the exact identity `PS.identity` tends to zero as `N → ∞`
  when `f'` is bounded.
* **The Dirichlet kernel.** `∫_p^q ‖K‖ ≤ 4 + 4 log(H₂ − H₁ + 1)` over any window of
  length at most one.
* **The tails.** For half-integers `p ≤ q` and `f'` decreasing with `H₁ < f' < H₂`,
  `‖∑_{h ∉ [H₁, H₂], |h| ≤ N} ∫_p^q e(f − hx)‖ ≤ 4/π + (2/π) log(H₂ − H₁ + 1)`,
  by one integration by parts per `h`: the boundary sums are alternating series
  (since `e(−hq) = (−1)^h`) and the integrals give `∫ (−f'')/(H₂ + 1 − f') = [log]`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace PS

open Sawtooth EM

/-! ### The Euler–Maclaurin error -/

/-- For a nonnegative, integrable, `1`-periodic `g`, `∫_p^q g ≤ (⌊q⌋ − ⌊p⌋ + 1) ∫_0^1 g`. -/
theorem integral_periodic_le {g : ℝ → ℝ} (hg : Function.Periodic g 1) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q) {p q : ℝ} (hpq : p ≤ q) :
    ∫ x in p..q, g x ≤ ((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) * ∫ x in (0 : ℝ)..1, g x := by
  have hfl := Int.floor_le_floor hpq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊q⌋ = ⌊p⌋ + n := ⟨(⌊q⌋ - ⌊p⌋).toNat, by omega⟩
  have h1 : ∫ x in p..q, g x ≤ ∫ x in (⌊p⌋ : ℝ)..((⌊p⌋ : ℝ) + ((n + 1 : ℕ) : ℝ)), g x := by
    apply integral_mono_interval (Int.floor_le p) hpq
    · have := Int.lt_floor_add_one q
      rw [hn] at this
      push_cast at this ⊢
      linarith
    · exact Filter.Eventually.of_forall hg0
    · exact hgi _ _
  have h2 : ∫ x in (⌊p⌋ : ℝ)..((⌊p⌋ : ℝ) + ((n + 1 : ℕ) : ℝ)), g x =
      ∑ k ∈ Finset.range (n + 1), ∫ x in ((⌊p⌋ : ℝ) + k)..((⌊p⌋ : ℝ) + k + 1), g x := by
    have := sum_integral_adjacent_intervals (μ := volume) (f := g)
      (a := fun k : ℕ => (⌊p⌋ : ℝ) + k) (n := n + 1) (fun k _ => hgi _ _)
    simp only [Nat.cast_zero, add_zero, Nat.cast_succ] at this
    push_cast
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring
  have h3 : ∀ k : ℕ, ∫ x in ((⌊p⌋ : ℝ) + k)..((⌊p⌋ : ℝ) + k + 1), g x = ∫ x in (0 : ℝ)..1, g x := by
    intro k
    have := hg.intervalIntegral_add_eq ((⌊p⌋ : ℝ) + k) 0
    simpa using this
  rw [h2, Finset.sum_congr rfl (fun k _ => h3 k), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  rw [hn]
  push_cast
  ring

theorem periodic_abs_ψ_add_S (N : ℕ) : Function.Periodic (fun x => |ψ x + S N x|) 1 := by
  intro x
  simp only
  rw [S_add_one, show (x + 1) = x + ((1 : ℤ) : ℝ) by push_cast; ring, ψ_add_int]

theorem measurable_S (N : ℕ) : Measurable (S N) :=
  (continuous_iff_continuousAt.2 fun x => (hasDerivAt_S N x).continuousAt).measurable

theorem intervalIntegrable_abs_ψ_add_S (N : ℕ) (p q : ℝ) :
    IntervalIntegrable (fun x => |ψ x + S N x|) volume p q :=
  Perron.intervalIntegrable_of_bounded (continuous_abs.measurable.comp (measurable_ψ.add (measurable_S N)))
    (fun x => by
      simp only [Function.comp_apply, Pi.add_apply, abs_abs]
      exact abs_ψ_add_S_le N x) p q

/-- `∫_0^1 |ψ + S_N| ≤ (9 + 8 log N)/N` for `N ≥ 2`. -/
theorem integral_abs_ψ_add_S_le {N : ℕ} (hN : 2 ≤ N) :
    ∫ x in (0 : ℝ)..1, |ψ x + S N x| ≤ (9 + 8 * Real.log N) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : 1 ≤ N := by omega
  set δ : ℝ := 1 / N with hδ
  have hδ0 : 0 < δ := by positivity
  have hδh : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hN0 (by norm_num)]
    linarith
  have hi : ∀ p q : ℝ, IntervalIntegrable (fun x => |ψ x + S N x|) volume p q :=
    intervalIntegrable_abs_ψ_add_S N
  -- the four pieces
  have hsplit : ∫ x in (0 : ℝ)..1, |ψ x + S N x| =
      (∫ x in (0 : ℝ)..δ, |ψ x + S N x|) + (∫ x in δ..(1 / 2 : ℝ), |ψ x + S N x|) +
        (∫ x in (1 / 2 : ℝ)..(1 - δ), |ψ x + S N x|) + ∫ x in (1 - δ)..(1 : ℝ), |ψ x + S N x| := by
    rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have hp1 : ∫ x in (0 : ℝ)..δ, |ψ x + S N x| ≤ 9 / 2 * δ := by
    have := integral_mono_on hδ0.le (hi _ _) intervalIntegrable_const
      (fun x _ => abs_ψ_add_S_le N x)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    linarith
  have hp4 : ∫ x in (1 - δ)..(1 : ℝ), |ψ x + S N x| ≤ 9 / 2 * δ := by
    have := integral_mono_on (by linarith : 1 - δ ≤ (1 : ℝ)) (hi _ _) intervalIntegrable_const
      (fun x _ => abs_ψ_add_S_le N x)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  -- the middle pieces
  have hbound : ∀ x ∈ Set.Icc δ (1 / 2 : ℝ), |ψ x + S N x| ≤ 4 / N * (1 / x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
    have hx1 : x < 1 := by linarith [hx.2]
    have hψ : ψ x = x - 1 / 2 := by
      have := ψ_eq_of_floor (x := x) (n := 0) (by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith)
      rw [this]; push_cast; ring
    rw [hψ]
    have := sawtooth_expansion hN1 hx0 hx1
    rw [min_eq_left (by linarith [hx.2])] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  have hcont : ContinuousOn (fun x : ℝ => 4 / N * (1 / x)) (Set.Icc δ (1 / 2)) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact (lt_of_lt_of_le hδ0 hx.1).ne'
  have hlog : ∫ x in δ..(1 / 2 : ℝ), 4 / N * (1 / x) = 4 / N * Real.log (N / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hδ0 (by norm_num)]
    congr 2
    rw [hδ]
    field_simp
  have hp2 : ∫ x in δ..(1 / 2 : ℝ), |ψ x + S N x| ≤ 4 / N * Real.log (N / 2) := by
    rw [← hlog]
    exact integral_mono_on hδh (hi _ _)
      (hcont.intervalIntegrable_of_Icc hδh) hbound
  have hp3 : ∫ x in (1 / 2 : ℝ)..(1 - δ), |ψ x + S N x| ≤ 4 / N * Real.log (N / 2) := by
    have hrefl : ∫ x in (1 / 2 : ℝ)..(1 - δ), |ψ x + S N x| =
        ∫ x in δ..(1 / 2 : ℝ), |ψ (1 - x) + S N (1 - x)| := by
      have := integral_comp_sub_left (a := δ) (b := 1 / 2) (fun x => |ψ x + S N x|) 1
      rw [this]
      norm_num
    rw [hrefl, ← hlog]
    apply integral_mono_on hδh
    · exact Perron.intervalIntegrable_of_bounded
        (continuous_abs.measurable.comp ((measurable_ψ.comp (measurable_const.sub measurable_id)).add
          ((measurable_S N).comp (measurable_const.sub measurable_id))))
        (fun x => by
          simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, id, abs_abs]
          exact abs_ψ_add_S_le N (1 - x)) _ _
    · exact hcont.intervalIntegrable_of_Icc hδh
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
      have hx1 : x < 1 := by linarith [hx.2]
      have hs : S N (1 - x) = -S N x := by
        rw [show (1 - x) = -x + 1 by ring, S_add_one, S_neg]
      have hψ : ψ (1 - x) = 1 / 2 - x := by
        have := ψ_eq_of_floor (x := 1 - x) (n := 0)
          (by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith)
        rw [this]; push_cast; ring
      rw [hs, hψ, show 1 / 2 - x + -S N x = -((x - 1 / 2) + S N x) by ring, abs_neg]
      have := sawtooth_expansion hN1 hx0 hx1
      rw [min_eq_left (by linarith [hx.2])] at this
      refine this.trans (le_of_eq ?_)
      field_simp
  have hlog2 : Real.log (N / 2) ≤ Real.log N := by
    apply Real.log_le_log (by positivity)
    linarith
  have h4N : 0 ≤ 4 / (N : ℝ) := by positivity
  rw [hsplit]
  calc _ ≤ 9 / 2 * δ + 4 / N * Real.log (N / 2) + 4 / N * Real.log (N / 2) + 9 / 2 * δ :=
        add_le_add (add_le_add (add_le_add hp1 hp2) hp3) hp4
    _ ≤ 9 / 2 * δ + 4 / N * Real.log N + 4 / N * Real.log N + 9 / 2 * δ := by
        gcongr
    _ = (9 + 8 * Real.log N) / N := by
        rw [hδ]
        field_simp
        ring

/-- The Euler–Maclaurin error term of `PS.identity` on `[p, q]`, for `|f'| ≤ L` there. -/
theorem norm_two_pi_I : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem norm_eD (f : ℝ → ℝ) (x : ℝ) : ‖eD f x‖ = 2 * π * |deriv f x| := by
  unfold eD
  rw [norm_mul, norm_mul, norm_two_pi_I, Complex.norm_real, Real.norm_eq_abs, norm_e_one, mul_one]

theorem norm_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {p q L : ℝ} (hpq : p ≤ q)
    (hL : ∀ x ∈ Set.Icc p q, |deriv f x| ≤ L) {N : ℕ} (hN : 2 ≤ N) :
    ‖∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x‖ ≤
      2 * π * L * ((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) * ((9 + 8 * Real.log N) / N) := by
  have hS : Continuous (S N) := continuous_iff_continuousAt.2 fun x => (hasDerivAt_S N x).continuousAt
  have hint : IntervalIntegrable (fun x => ((ψ x + S N x : ℝ) : ℂ) * eD f x) volume p q := by
    have h1 := EM.intervalIntegrable_ψ_mul (continuous_eD hf) p q
    have h2 : IntervalIntegrable (fun x => ((S N x : ℝ) : ℂ) * eD f x) volume p q :=
      ((Complex.continuous_ofReal.comp hS).mul (continuous_eD hf)).intervalIntegrable p q
    have := h1.add h2
    refine this.congr ?_
    intro x _
    show ((ψ x : ℝ) : ℂ) * eD f x + ((S N x : ℝ) : ℂ) * eD f x = ((ψ x + S N x : ℝ) : ℂ) * eD f x
    push_cast
    ring
  have hL0 : 0 ≤ L := by
    have := hL p ⟨le_rfl, hpq⟩
    exact (abs_nonneg _).trans this
  calc ‖∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x‖
      ≤ ∫ x in p..q, ‖((ψ x + S N x : ℝ) : ℂ) * eD f x‖ := norm_integral_le_integral_norm hpq
    _ ≤ ∫ x in p..q, 2 * π * L * |ψ x + S N x| := by
        apply integral_mono_on hpq hint.norm
          ((intervalIntegrable_abs_ψ_add_S N p q).const_mul _)
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_eD]
        have h1 := hL x hx
        have h2 := abs_nonneg (ψ x + S N x)
        have h3 : |ψ x + S N x| * |deriv f x| ≤ |ψ x + S N x| * L :=
          mul_le_mul_of_nonneg_left h1 h2
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * π)
        linarith
    _ = 2 * π * L * ∫ x in p..q, |ψ x + S N x| := intervalIntegral.integral_const_mul _ _
    _ ≤ 2 * π * L * (((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) * ∫ x in (0 : ℝ)..1, |ψ x + S N x|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_periodic_le (periodic_abs_ψ_add_S N) (fun x => abs_nonneg _)
          (intervalIntegrable_abs_ψ_add_S N) hpq
    _ ≤ 2 * π * L * (((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) * ((9 + 8 * Real.log N) / N)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hfl := Int.floor_le_floor hpq
        have hc0 : (0 : ℝ) ≤ ((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) := by
          exact_mod_cast (by omega : (0 : ℤ) ≤ ⌊q⌋ - ⌊p⌋ + 1)
        exact mul_le_mul_of_nonneg_left (integral_abs_ψ_add_S_le hN) hc0
    _ = _ := by ring

/-! ### The Dirichlet kernel over a unit window -/

theorem K_periodic (H₁ H₂ : ℤ) : Function.Periodic (K H₁ H₂) 1 := by
  intro x
  unfold K
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [show -((h : ℝ) * (x + 1)) = -((h : ℝ) * x) - ((h : ℤ) : ℝ) by push_cast; ring, KL.e_sub_int]

theorem le_nearestIntDist_of_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : x ≤ nearestIntDist x := by
  unfold nearestIntDist
  rcases le_or_gt (round x) 0 with h | h
  · have : ((round x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (1 : ℝ) ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- `∫_p^q ‖K‖ ≤ 4 + 4 log(H₂ − H₁ + 1)` for `q − p ≤ 1`. -/
theorem integral_norm_K_le {H₁ H₂ : ℤ} (h12 : H₁ ≤ H₂) {p q : ℝ} (hpq : p ≤ q)
    (hlen : q ≤ p + 1) :
    ∫ x in p..q, ‖K H₁ H₂ x‖ ≤ 4 + 4 * Real.log ((H₂ : ℝ) - H₁ + 1) := by
  set M : ℝ := (H₂ : ℝ) - H₁ + 1 with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : (H₁ : ℝ) ≤ H₂ := by exact_mod_cast h12
    linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hKc : Continuous fun x => ‖K H₁ H₂ x‖ := (continuous_K H₁ H₂).norm
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun x => ‖K H₁ H₂ x‖) volume u v :=
    fun u v => hKc.intervalIntegrable u v
  have hcard : ∀ x, ‖K H₁ H₂ x‖ ≤ M := fun x => norm_K_le_card h12 x
  rcases le_or_gt M 4 with hM4 | hM4
  · -- trivial bound
    have := integral_mono_on hpq (hi _ _) intervalIntegrable_const (fun x _ => hcard x) |>.trans
      (le_of_eq (intervalIntegral.integral_const M))
    rw [smul_eq_mul] at this
    have h2 : (q - p) * M ≤ 1 * 4 := by
      apply mul_le_mul (by linarith) hM4 (by linarith) (by norm_num)
    linarith
  -- reduce to `[-1/2, 1/2]`
  set δ : ℝ := 2 / M with hδ
  have hδ0 : 0 < δ := by positivity
  have hδh : δ < 1 / 2 := by
    rw [hδ, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1 : ∫ x in p..q, ‖K H₁ H₂ x‖ ≤ ∫ x in p..(p + 1), ‖K H₁ H₂ x‖ :=
    integral_mono_interval le_rfl hpq hlen (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (hi _ _)
  have hKp : Function.Periodic (fun x => ‖K H₁ H₂ x‖) 1 := fun x => by
    simp only
    rw [K_periodic H₁ H₂ x]
  have h2 : ∫ x in p..(p + 1), ‖K H₁ H₂ x‖ = ∫ x in (-(1 / 2) : ℝ)..(-(1 / 2) + 1), ‖K H₁ H₂ x‖ :=
    hKp.intervalIntegral_add_eq p (-(1 / 2))
  have hsplit : ∫ x in (-(1 / 2) : ℝ)..(-(1 / 2) + 1), ‖K H₁ H₂ x‖ =
      (∫ x in (-(1 / 2) : ℝ)..(-δ), ‖K H₁ H₂ x‖) + (∫ x in (-δ)..δ, ‖K H₁ H₂ x‖) +
        ∫ x in δ..(-(1 / 2) + 1 : ℝ), ‖K H₁ H₂ x‖ := by
    rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  -- the pieces
  have hmid : ∫ x in (-δ)..δ, ‖K H₁ H₂ x‖ ≤ 4 := by
    have := integral_mono_on (by linarith : -δ ≤ δ) (hi _ _) intervalIntegrable_const
      (fun x _ => hcard x)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have : (δ - -δ) * M = 4 := by
      rw [hδ]
      first | (field_simp; done) | (field_simp; ring)
    linarith
  have hcont : ContinuousOn (fun x : ℝ => 2 * (1 / x)) (Set.Icc δ (1 / 2)) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact (lt_of_lt_of_le hδ0 hx.1).ne'
  have hlog : ∫ x in δ..(1 / 2 : ℝ), 2 * (1 / x) = 2 * Real.log (M / 4) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hδ0 (by norm_num)]
    congr 2
    rw [hδ]
    first | (field_simp; done) | (field_simp; ring)
  have hlogM4 : Real.log (M / 4) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    linarith
  have hptwise : ∀ x ∈ Set.Icc δ (1 / 2 : ℝ), ‖K H₁ H₂ x‖ ≤ 2 * (1 / x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
    have hnd : x ≤ nearestIntDist x := le_nearestIntDist_of_half hx0.le hx.2
    calc ‖K H₁ H₂ x‖ ≤ 2 / nearestIntDist x := norm_K_le_inv h12 (lt_of_lt_of_le hx0 hnd)
      _ ≤ 2 / x := by gcongr
      _ = 2 * (1 / x) := by ring
  have hright : ∫ x in δ..(-(1 / 2) + 1 : ℝ), ‖K H₁ H₂ x‖ ≤ 2 * Real.log M := by
    rw [show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num]
    calc ∫ x in δ..(1 / 2 : ℝ), ‖K H₁ H₂ x‖ ≤ ∫ x in δ..(1 / 2 : ℝ), 2 * (1 / x) :=
          integral_mono_on hδh.le (hi _ _) (hcont.intervalIntegrable_of_Icc hδh.le) hptwise
      _ = 2 * Real.log (M / 4) := hlog
      _ ≤ 2 * Real.log M := by linarith
  have hleft : ∫ x in (-(1 / 2) : ℝ)..(-δ), ‖K H₁ H₂ x‖ ≤ 2 * Real.log M := by
    have hrefl : ∫ x in (-(1 / 2) : ℝ)..(-δ), ‖K H₁ H₂ x‖ =
        ∫ x in δ..(1 / 2 : ℝ), ‖K H₁ H₂ (-x)‖ := by
      rw [integral_comp_neg (fun x => ‖K H₁ H₂ x‖)]
    rw [hrefl]
    calc ∫ x in δ..(1 / 2 : ℝ), ‖K H₁ H₂ (-x)‖ ≤ ∫ x in δ..(1 / 2 : ℝ), 2 * (1 / x) := by
          apply integral_mono_on hδh.le
          · exact (hKc.comp continuous_neg).intervalIntegrable _ _
          · exact hcont.intervalIntegrable_of_Icc hδh.le
          · intro x hx
            have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
            have hnd : x ≤ nearestIntDist x := le_nearestIntDist_of_half hx0.le hx.2
            calc ‖K H₁ H₂ (-x)‖ ≤ 2 / nearestIntDist (-x) :=
                  norm_K_le_inv h12 (by rw [KL.nearestIntDist_neg]; exact lt_of_lt_of_le hx0 hnd)
              _ = 2 / nearestIntDist x := by rw [KL.nearestIntDist_neg]
              _ ≤ 2 / x := by gcongr
              _ = 2 * (1 / x) := by ring
      _ = 2 * Real.log (M / 4) := hlog
      _ ≤ 2 * Real.log M := by linarith
  calc ∫ x in p..q, ‖K H₁ H₂ x‖ ≤ _ := h1
    _ = _ := h2
    _ = _ := hsplit
    _ ≤ 2 * Real.log M + 4 + 2 * Real.log M := add_le_add (add_le_add hleft hmid) hright
    _ = 4 + 4 * Real.log M := by ring

/-- The main-term integrals over a short window: `‖∑_h ∫_p^q e(f − hx)‖ ≤ 4 + 4 log(H₂ − H₁ + 1)`. -/
theorem norm_sum_integral_short {f : ℝ → ℝ} (hf : Continuous f) {H₁ H₂ : ℤ} (h12 : H₁ ≤ H₂)
    {p q : ℝ} (hpq : p ≤ q) (hlen : q ≤ p + 1) :
    ‖∑ h ∈ Finset.Icc H₁ H₂, ∫ x in p..q, e (f x - h * x)‖ ≤
      4 + 4 * Real.log ((H₂ : ℝ) - H₁ + 1) := by
  have hint : ∀ h ∈ Finset.Icc H₁ H₂, IntervalIntegrable (fun x => e (f x - h * x)) volume p q :=
    fun h _ => (continuous_e_comp (hf.sub (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [← integral_finset_sum hint]
  have heq : ∀ x, ∑ h ∈ Finset.Icc H₁ H₂, e (f x - h * x) = e (f x) * K H₁ H₂ x := by
    intro x
    unfold K
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [sub_eq_add_neg, KL.e_add]
  simp_rw [heq]
  calc ‖∫ x in p..q, e (f x) * K H₁ H₂ x‖ ≤ ∫ x in p..q, ‖e (f x) * K H₁ H₂ x‖ :=
        norm_integral_le_integral_norm hpq
    _ = ∫ x in p..q, ‖K H₁ H₂ x‖ := by
        apply integral_congr
        intro x _
        simp only
        rw [norm_mul, norm_e_one, one_mul]
    _ ≤ _ := integral_norm_K_le h12 hpq hlen

/-! ### The sign of `f''` -/

/-- If `f ∈ C²` and `f'` is antitone on `[a, b]` with `a < b`, then `f'' ≤ 0` on `[a, b]`. -/
theorem deriv2_nonpos {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : ℝ} (hab : a < b)
    (hanti : AntitoneOn (deriv f) (Set.Icc a b)) :
    ∀ x ∈ Set.Icc a b, deriv (deriv f) x ≤ 0 := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hd : ∀ x, HasDerivAt (fun y => -deriv f y) (-deriv (deriv f) x) x :=
    fun x => ((hf1.differentiable one_ne_zero) x).hasDerivAt.neg
  have hmono : MonotoneOn (fun y => -deriv f y) (Set.Icc a b) := by
    intro x hx y hy hxy
    simp only
    linarith [hanti hx hy hxy]
  have hopen : ∀ x ∈ Set.Ioo a b, deriv (deriv f) x ≤ 0 := by
    intro x hx
    have := (hd x).hasDerivWithinAt.nonneg_of_monotoneOn (GK31.accPt_Icc hx) hmono
    linarith
  have hc : Continuous (deriv (deriv f)) := hf1.continuous_deriv le_rfl
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hax | hax
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · exact hopen x ⟨hax, hxb⟩
    · -- `x = b`: limit from the left
      have hlim : Filter.Tendsto (deriv (deriv f)) (nhdsWithin x (Set.Ioo a x))
          (nhds (deriv (deriv f) x)) :=
        hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hne : (nhdsWithin x (Set.Ioo a x)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hax.ne]
        exact ⟨hax.le, le_rfl⟩
      exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy =>
        hopen y ⟨hy.1, hy.2.trans_le hx.2⟩)
  · -- `x = a`: limit from the right
    have hxb : x < b := by rw [← hax]; exact hab
    have hlim : Filter.Tendsto (deriv (deriv f)) (nhdsWithin x (Set.Ioo x b))
        (nhds (deriv (deriv f) x)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hne : (nhdsWithin x (Set.Ioo x b)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hxb.ne]
      exact ⟨le_rfl, hxb.le⟩
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy =>
      hopen y ⟨hx.1.trans_lt hy.1, hy.2⟩)

/-! ### Integration by parts for `∫ e(φ)` -/

theorem parts_phase {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x) (hφ'c : Continuous φ') (hφ''c : Continuous φ'')
    {p q : ℝ} (hpq : p ≤ q) (hne : ∀ x ∈ Set.Icc p q, φ' x ≠ 0) :
    ∫ x in p..q, e (φ x) =
      e (φ q) * ((1 / φ' q : ℝ) : ℂ) / (2 * π * Complex.I) -
        e (φ p) * ((1 / φ' p : ℝ) : ℂ) / (2 * π * Complex.I) +
        (1 / (2 * π * Complex.I)) * ∫ x in p..q, e (φ x) * ((φ'' x / (φ' x) ^ 2 : ℝ) : ℂ) := by
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  -- `u = (1/φ')/(2πi)`, `v = e∘φ`
  have hu : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun x => ((1 / φ' x : ℝ) : ℂ) / (2 * π * Complex.I))
        (((-φ'' x / (φ' x) ^ 2 : ℝ) : ℂ) / (2 * π * Complex.I)) x := by
    intro x hx
    rw [hIcc] at hx
    have h1 : HasDerivAt (fun x => (φ' x)⁻¹) (-φ'' x / (φ' x) ^ 2) x := (hφ' x).inv (hne x hx)
    have h2 := (h1.ofReal_comp).div_const (2 * π * Complex.I)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [one_div]
  have hv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun x => e (φ x)) (2 * π * Complex.I * φ' x * e (φ x)) x :=
    fun x _ => hasDerivAt_e_comp (hφ x)
  have hcont1 : ContinuousOn (fun x => ((-φ'' x / (φ' x) ^ 2 : ℝ) : ℂ) / (2 * π * Complex.I))
      (Set.uIcc p q) := by
    rw [hIcc]
    apply ContinuousOn.div_const
    apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.div (hφ''c.neg.continuousOn) (hφ'c.pow 2).continuousOn
    intro x hx
    exact pow_ne_zero 2 (hne x hx)
  have hcont2 : Continuous (fun x => (2 * π * Complex.I * φ' x * e (φ x))) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hφ'c)).mul
      (continuous_e_comp (continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hcont1.intervalIntegrable
    (hcont2.intervalIntegrable _ _)
  have hL : ∫ x in p..q, ((1 / φ' x : ℝ) : ℂ) / (2 * π * Complex.I) *
      (2 * π * Complex.I * φ' x * e (φ x)) = ∫ x in p..q, e (φ x) := by
    apply integral_congr
    intro x hx
    rw [hIcc] at hx
    simp only
    have : (φ' x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    push_cast
    field_simp
  have hR : ∫ x in p..q, ((-φ'' x / (φ' x) ^ 2 : ℝ) : ℂ) / (2 * π * Complex.I) * e (φ x) =
      -((1 / (2 * π * Complex.I)) * ∫ x in p..q, e (φ x) * ((φ'' x / (φ' x) ^ 2 : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply integral_congr
    intro x _
    simp only
    push_cast
    ring
  rw [hL, hR] at h
  rw [h]
  ring

/-! ### The alternating tail sums -/

theorem neg_one_zpow_neg (j : ℤ) : (-1 : ℝ) ^ (-j) = (-1) ^ j := by
  rw [zpow_neg]
  rcases Int.even_or_odd j with he | ho
  · rw [he.neg_one_zpow, inv_one]
  · rw [ho.neg_one_zpow]
    norm_num

/-- `|∑_{j ≤ n} (−1)^{m+j} / (c − (m + j))| ≤ 1/(m − c)` for `c < m`. -/
theorem abs_alt_plus_le (c : ℝ) (m : ℤ) (n : ℕ) (hmc : c < m) :
    |∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (m + (j : ℤ)) / (c - ((m + (j : ℤ) : ℤ) : ℝ))| ≤
      1 / ((m : ℝ) - c) := by
  set u : ℕ → ℝ := fun j => 1 / ((j : ℝ) + ((m : ℝ) - c)) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by rw [hu]; positivity
  have huanti : Antitone u := by
    intro i j hij
    rw [hu]
    simp only
    apply one_div_le_one_div_of_le (by positivity)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have heq : ∀ j : ℕ, (-1 : ℝ) ^ (m + (j : ℤ)) / (c - ((m + (j : ℤ) : ℤ) : ℝ)) =
      -((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ j * u j) := by
    intro j
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_natCast, hu]
    simp only
    push_cast
    have : c - ((m : ℝ) + j) ≠ 0 := by linarith
    have : (j : ℝ) + ((m : ℝ) - c) ≠ 0 := by linarith
    first | (field_simp; done) | (field_simp; ring)
  simp_rw [heq]
  rw [← Finset.mul_sum, abs_mul, abs_neg, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have := abs_alt_sum_le u huanti hu0 (n + 1)
  refine this.trans (le_of_eq ?_)
  rw [hu]
  simp

/-- `|∑_{j ≤ n} (−1)^{m−j} / (c − (m − j))| ≤ 1/(c − m)` for `m < c`. -/
theorem abs_alt_minus_le (c : ℝ) (m : ℤ) (n : ℕ) (hmc : (m : ℝ) < c) :
    |∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (m - (j : ℤ)) / (c - ((m - (j : ℤ) : ℤ) : ℝ))| ≤
      1 / (c - m) := by
  set u : ℕ → ℝ := fun j => 1 / ((j : ℝ) + (c - m)) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by rw [hu]; positivity
  have huanti : Antitone u := by
    intro i j hij
    rw [hu]
    simp only
    apply one_div_le_one_div_of_le (by positivity)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have heq : ∀ j : ℕ, (-1 : ℝ) ^ (m - (j : ℤ)) / (c - ((m - (j : ℤ) : ℤ) : ℝ)) =
      ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ j * u j) := by
    intro j
    rw [zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_natCast, hu]
    simp only
    push_cast
    have h1 : ((-1 : ℝ) ^ j)⁻¹ = (-1) ^ j := by
      rcases Nat.even_or_odd j with he | ho
      · rw [he.neg_one_pow, inv_one]
      · rw [ho.neg_one_pow]
        norm_num
    have : c - ((m : ℝ) - j) ≠ 0 := by linarith
    have : (j : ℝ) + (c - m) ≠ 0 := by linarith
    rw [div_eq_mul_inv ((-1 : ℝ) ^ m), h1]
    first | (field_simp; done) | (field_simp; ring)
  simp_rw [heq]
  rw [← Finset.mul_sum, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have := abs_alt_sum_le u huanti hu0 (n + 1)
  refine this.trans (le_of_eq ?_)
  rw [hu]
  simp

/-- Reindexing `Icc (m − n) m` downwards. -/
theorem sum_Icc_eq_sum_range_rev (F : ℤ → ℝ) (m : ℤ) (n : ℕ) :
    ∑ h ∈ Finset.Icc (m - n) m, F h = ∑ j ∈ Finset.range (n + 1), F (m - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Finset.Icc (m - ((n + 1 : ℕ) : ℤ)) m = insert (m - (n : ℤ) - 1) (Finset.Icc (m - n) m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_range_succ _ (n + 1), add_comm]
    congr 1
    congr 1
    push_cast
    ring

theorem sum_Icc_eq_sum_range_real (F : ℤ → ℝ) (H₁ : ℤ) (n : ℕ) :
    ∑ h ∈ Finset.Icc H₁ (H₁ + n), F h = ∑ j ∈ Finset.range (n + 1), F (H₁ + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Finset.Icc H₁ (H₁ + ((n + 1 : ℕ) : ℤ)) =
        insert (H₁ + (n : ℤ) + 1) (Finset.Icc H₁ (H₁ + n)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert (by simp), ih, Finset.sum_range_succ _ (n + 1)]
    push_cast
    rw [add_comm, show H₁ + ((n : ℤ) + 1) = H₁ + n + 1 by ring]

/-- The boundary sum at a half-integer `q = mq + 1/2`: for `H₁ < c < H₂`,
`|∑_{h ∈ T} (−1)^h/(c − h)| ≤ 2` where `T = [−N, H₁ − 1] ∪ [H₂ + 1, N]`. -/
theorem abs_boundary_sum_le {H₁ H₂ : ℤ} {N : ℕ} (h1 : -(N : ℤ) ≤ H₁) (h2 : H₂ ≤ N)
    {c : ℝ} (hc1 : (H₁ : ℝ) < c) (hc2 : c < H₂) :
    |∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
        (-1 : ℝ) ^ h / (c - h)| ≤ 2 := by
  have h12 : H₁ ≤ H₂ := by
    have : (H₁ : ℝ) < H₂ := hc1.trans hc2
    exact_mod_cast this.le
  rw [Finset.sum_union (disjoint_Icc_Icc h12)]
  have hA : |∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1), (-1 : ℝ) ^ h / (c - h)| ≤ 1 := by
    rcases le_or_gt (-(N : ℤ)) (H₁ - 1) with hle | hlt
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, -(N : ℤ) = (H₁ - 1) - n := ⟨((H₁ - 1) + N).toNat, by omega⟩
      rw [hn, sum_Icc_eq_sum_range_rev]
      have := abs_alt_minus_le c (H₁ - 1) n (by push_cast; linarith)
      refine this.trans ?_
      rw [div_le_one (by push_cast; linarith)]
      push_cast
      linarith
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero]
      norm_num
  have hB : |∑ h ∈ Finset.Icc (H₂ + 1) N, (-1 : ℝ) ^ h / (c - h)| ≤ 1 := by
    rcases le_or_gt (H₂ + 1) (N : ℤ) with hle | hlt
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (N : ℤ) = (H₂ + 1) + n := ⟨(N - (H₂ + 1)).toNat, by omega⟩
      rw [hn, sum_Icc_eq_sum_range_real]
      have := abs_alt_plus_le c (H₂ + 1) n (by push_cast; linarith)
      refine this.trans ?_
      rw [div_le_one (by push_cast; linarith)]
      push_cast
      linarith
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero]
      norm_num
  calc _ ≤ |∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1), (-1 : ℝ) ^ h / (c - h)| +
        |∑ h ∈ Finset.Icc (H₂ + 1) N, (-1 : ℝ) ^ h / (c - h)| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add hA hB
    _ = 2 := by norm_num

/-- `∑_{h ∈ T} 1/(c − h)² ≤ 2/(H₂ + 1 − c) + 2/(c − H₁ + 1)` for `H₁ < c < H₂`. -/
theorem sum_inv_sq_tail_le {H₁ H₂ : ℤ} {N : ℕ} (h1 : -(N : ℤ) ≤ H₁) (h2 : H₂ ≤ N)
    {c : ℝ} (hc1 : (H₁ : ℝ) < c) (hc2 : c < H₂) :
    ∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N, 1 / (c - h) ^ 2 ≤
      2 / (1 + ((H₂ : ℝ) - c)) + 2 / (1 + (c - H₁)) := by
  have h12 : H₁ ≤ H₂ := by
    have : (H₁ : ℝ) < H₂ := hc1.trans hc2
    exact_mod_cast this.le
  rw [Finset.sum_union (disjoint_Icc_Icc h12)]
  have hA : ∑ h ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1), 1 / (c - h) ^ 2 ≤ 2 / (1 + (c - H₁)) := by
    rcases le_or_gt (-(N : ℤ)) (H₁ - 1) with hle | hlt
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, -(N : ℤ) = (H₁ - 1) - n := ⟨((H₁ - 1) + N).toNat, by omega⟩
      rw [hn, sum_Icc_eq_sum_range_rev]
      have := sum_inv_sq_le (u := c - H₁) (by linarith) (n + 1)
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      congr 1
      ring
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
  have hB : ∑ h ∈ Finset.Icc (H₂ + 1) N, 1 / (c - h) ^ 2 ≤ 2 / (1 + ((H₂ : ℝ) - c)) := by
    rcases le_or_gt (H₂ + 1) (N : ℤ) with hle | hlt
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (N : ℤ) = (H₂ + 1) + n := ⟨(N - (H₂ + 1)).toNat, by omega⟩
      rw [hn, sum_Icc_eq_sum_range_real]
      have := sum_inv_sq_le (u := (H₂ : ℝ) - c) (by linarith) (n + 1)
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      congr 1
      ring
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
  linarith

end PS

end LeanProofs.IntegerPoints
