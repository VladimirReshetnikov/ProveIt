import IntegerPoints.PoissonTail
import IntegerPoints.GKStatements

/-!
# Graham–Kolesnik, Lemma 3.5 (truncated Poisson summation)

`∑_{a < n ≤ b} e(f(n)) = ∑_{H₁ ≤ h ≤ H₂} ∫_a^b e(f(x) − hx) dx + O(log(H₂ − H₁))`
when `f ∈ C²`, `f'` is decreasing and `H₁ < f' < H₂` on `[a, b]`, `H₂ − H₁ ≥ 2`.

**Proof.**  Let `a₁` be the smallest half-integer `≥ a` and `b₁` the largest half-integer
`≤ b`.  The windows `(a, a₁]` and `(b₁, b]` contain at most one integer each, and the
main-term integrals over them are bounded by the `L¹` norm of the Dirichlet kernel,
`4 + 4 log(H₂ − H₁ + 1)` (`PS.norm_sum_integral_short`).  On `[a₁, b₁]`, the exact
identity `PS.identity` with truncation `N` expresses the sum as
`∑_{|k| ≤ N} ∫ e(f − kx) + (boundary) + (error_N)`; the tail `|k| ≤ N`, `k ∉ [H₁, H₂]` is
bounded by `PS.tail_bound` (this is where half-integer endpoints are used), the boundary
terms are at most `9`, and `error_N → 0` as `N → ∞` (`PS.norm_error_le`).
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace GK35

open PS Sawtooth EM

theorem tendsto_aux (K : ℝ) :
    Filter.Tendsto (fun N : ℕ => K * ((9 + 8 * Real.log N) / N)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (9 : ℝ) / N) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 9
  have h2 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Filter.Tendsto (fun N : ℕ => Real.log N / N) Filter.atTop (nhds 0) := by
    have := h2.comp tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp [Function.comp]
  have h4 := (h1.add (h3.const_mul 8)).const_mul K
  simp only [mul_zero, add_zero] at h4
  refine h4.congr fun N => ?_
  ring

/-- The sum over `(a, b]` as a sum over integers. -/
theorem sum_intRange_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ) :
    ∑ n ∈ intRange a b, e (f n) = ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, e (f n) := by
  unfold intRange
  have hb : 0 ≤ b := ha.trans hab
  have hmap : Finset.map Nat.castEmbedding (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) = Finset.Ioc ⌊a⌋ ⌊b⌋ := by
    ext x
    simp only [Finset.mem_map, Finset.mem_Ioc, Nat.castEmbedding_apply]
    rw [← Int.natCast_floor_eq_floor ha, ← Int.natCast_floor_eq_floor hb]
    constructor
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      have hx0 : 0 ≤ x := by
        have : (0 : ℤ) ≤ (⌊a⌋₊ : ℤ) := by positivity
        omega
      refine ⟨x.toNat, ⟨?_, ?_⟩, Int.toNat_of_nonneg hx0⟩
      · have := Int.toNat_of_nonneg hx0
        omega
      · have := Int.toNat_of_nonneg hx0
        omega
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

theorem norm_sum_Ioc_le_one (F : ℝ → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {m n : ℤ} (hmn : n ≤ m + 1) :
    ‖∑ k ∈ Finset.Ioc m n, F k‖ ≤ 1 := by
  calc ‖∑ k ∈ Finset.Ioc m n, F k‖ ≤ ∑ k ∈ Finset.Ioc m n, ‖F k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ioc m n, (1 : ℝ) := Finset.sum_le_sum fun k _ => hF k
    _ = ((n - m).toNat : ℝ) := by rw [Finset.sum_const, Int.card_Ioc, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by
        have : (n - m).toNat ≤ 1 := by omega
        exact_mod_cast this

theorem sum_Ioc_split (F : ℤ → ℂ) {m n k : ℤ} (h1 : m ≤ n) (h2 : n ≤ k) :
    ∑ i ∈ Finset.Ioc m k, F i = ∑ i ∈ Finset.Ioc m n, F i + ∑ i ∈ Finset.Ioc n k, F i := by
  rw [← Finset.sum_union]
  · congr 1
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_union]
    omega
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Ioc] at hx1 hx2
    omega

/-- The bound on a window `[p, q]` with half-integer endpoints. -/
theorem mid_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : ℝ} (hab : a < b)
    (hanti : AntitoneOn (deriv f) (Set.Icc a b)) {H₁ H₂ : ℤ}
    (hH : ∀ x ∈ Set.Icc a b, (H₁ : ℝ) < deriv f x ∧ deriv f x < H₂)
    {p q : ℝ} (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) {mp mq : ℤ}
    (hp : p = mp + 1 / 2) (hq : q = mq + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊p⌋ ⌊q⌋, e (f n)) -
        ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in p..q, e (f x - h * x)‖ ≤
      9 + 4 / π + (2 / π) * Real.log ((H₂ : ℝ) - H₁ + 1) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hsub : Set.Icc p q ⊆ Set.Icc a b := Set.Icc_subset_Icc hap hqb
  have h12 : H₁ ≤ H₂ := by
    have := hH p ⟨hap, hpq.trans hqb⟩
    have : (H₁ : ℝ) < H₂ := this.1.trans this.2
    exact_mod_cast this.le
  set L : ℝ := max |(H₁ : ℝ)| |(H₂ : ℝ)| with hL
  have hLb : ∀ x ∈ Set.Icc p q, |deriv f x| ≤ L := by
    intro x hx
    obtain ⟨h1, h2⟩ := hH x (hsub hx)
    rw [abs_le]
    constructor
    · have : -L ≤ -|(H₁ : ℝ)| := by rw [neg_le_neg_iff, hL]; exact le_max_left _ _
      have : -|(H₁ : ℝ)| ≤ H₁ := neg_abs_le _
      linarith
    · have : (H₂ : ℝ) ≤ |(H₂ : ℝ)| := le_abs_self _
      have : |(H₂ : ℝ)| ≤ L := by rw [hL]; exact le_max_right _ _
      linarith
  set K : ℝ := 2 * π * L * ((⌊q⌋ - ⌊p⌋ + 1 : ℤ) : ℝ) with hK
  set M : ℝ := (H₂ : ℝ) - H₁ + 1 with hM
  set X : ℂ := (∑ n ∈ Finset.Ioc ⌊p⌋ ⌊q⌋, e (f n)) -
    ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in p..q, e (f x - h * x) with hX
  have key : ∀ N : ℕ, 2 ≤ N → -(N : ℤ) ≤ H₁ → H₂ ≤ N →
      ‖X‖ ≤ (9 + 4 / π + (2 / π) * Real.log M) + K * ((9 + 8 * Real.log N) / N) := by
    intro N hN2 h1 h2
    have hid := PS.identity hf1 hpq N
    have hpair : (∫ x in p..q, e (f x)) +
        ∑ k ∈ Finset.range N, ∫ x in p..q, (e (f x + (k + 1) * x) + e (f x - (k + 1) * x)) =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∫ x in p..q, e (f x - k * x) := by
      rw [← sum_range_pair (fun k : ℤ => ∫ x in p..q, e (f x - k * x)) N]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hfc : Continuous f := hf.continuous
        have hi1 : IntervalIntegrable (fun x => e (f x - ((-((k : ℤ) + 1) : ℤ) : ℝ) * x)) volume p q :=
          (continuous_e_comp (by fun_prop)).intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun x => e (f x - (((k : ℤ) + 1 : ℤ) : ℝ) * x)) volume p q :=
          (continuous_e_comp (by fun_prop)).intervalIntegrable _ _
        rw [← intervalIntegral.integral_add hi1 hi2]
        apply integral_congr
        intro x _
        simp only
        push_cast
        ring_nf
    rw [hpair] at hid
    have hsplit : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∫ x in p..q, e (f x - k * x) =
        (∑ k ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
            ∫ x in p..q, e (f x - k * x)) +
          ∑ k ∈ Finset.Icc H₁ H₂, ∫ x in p..q, e (f x - k * x) := by
      rw [← Icc_sdiff_eq h1 h2 h12, Finset.sum_sdiff (Finset.Icc_subset_Icc h1 h2)]
    rw [hsplit] at hid
    have hXeq : X = (∑ k ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
          ∫ x in p..q, e (f x - k * x)) +
        ((ψ p + S N p : ℝ) : ℂ) * e (f p) - ((ψ q + S N q : ℝ) : ℂ) * e (f q) +
        ∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x := by
      rw [hX, hid]
      ring
    have htail := PS.tail_bound hf hab hanti hH hap hpq hqb hp hq h1 h2
    have hbp : ‖((ψ p + S N p : ℝ) : ℂ) * e (f p)‖ ≤ 9 / 2 := by
      rw [norm_mul, norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_ψ_add_S_le N p
    have hbq : ‖((ψ q + S N q : ℝ) : ℂ) * e (f q)‖ ≤ 9 / 2 := by
      rw [norm_mul, norm_e_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_ψ_add_S_le N q
    have herr := PS.norm_error_le hf1 hpq hLb hN2
    rw [hXeq]
    calc _ ≤ ‖(∑ k ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
            ∫ x in p..q, e (f x - k * x)) +
          ((ψ p + S N p : ℝ) : ℂ) * e (f p) - ((ψ q + S N q : ℝ) : ℂ) * e (f q)‖ +
          ‖∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x‖ := norm_add_le _ _
      _ ≤ (‖(∑ k ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
            ∫ x in p..q, e (f x - k * x)) + ((ψ p + S N p : ℝ) : ℂ) * e (f p)‖ +
          ‖((ψ q + S N q : ℝ) : ℂ) * e (f q)‖) +
          ‖∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ ((‖∑ k ∈ Finset.Icc (-(N : ℤ)) (H₁ - 1) ∪ Finset.Icc (H₂ + 1) N,
            ∫ x in p..q, e (f x - k * x)‖ + ‖((ψ p + S N p : ℝ) : ℂ) * e (f p)‖) +
          ‖((ψ q + S N q : ℝ) : ℂ) * e (f q)‖) +
          ‖∫ x in p..q, ((ψ x + S N x : ℝ) : ℂ) * eD f x‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (((4 / π + (2 / π) * Real.log M) + 9 / 2) + 9 / 2) + K * ((9 + 8 * Real.log N) / N) := by
          gcongr
      _ = _ := by ring
  -- let `N → ∞`
  have ht := (tendsto_aux K).const_add (9 + 4 / π + (2 / π) * Real.log M)
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  rw [Filter.eventually_atTop]
  refine ⟨2 + H₂.natAbs + H₁.natAbs, fun N hN => key N (by omega) (by omega) (by omega)⟩

end GK35

open GK35 PS Sawtooth EM in
/-- **Graham–Kolesnik, Lemma 3.5** holds with the absolute constant `55`. -/
theorem gk_lemma35_holds : gk_lemma35 := by
  refine ⟨55, ?_⟩
  intro a b H₁ H₂ f ha hab hf hanti hH hH12
  -- notation
  have hpi : (3 : ℝ) < π := BI.pi_gt_three'
  set H : ℝ := (H₂ : ℝ) - H₁ with hHdef
  have hH2 : (2 : ℝ) ≤ H := by
    rw [hHdef]
    have : ((H₁ + 2 : ℤ) : ℝ) ≤ H₂ := by exact_mod_cast hH12
    push_cast at this
    linarith
  have h12 : H₁ ≤ H₂ := by omega
  set M : ℝ := (H₂ : ℝ) - H₁ + 1 with hMdef
  have hlogM : Real.log M ≤ 2 * Real.log H := by
    have h2 : Real.log (H ^ 2) = 2 * Real.log H := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [← h2]
    apply Real.log_le_log (by rw [hMdef]; linarith)
    rw [hMdef]
    nlinarith
  have hlogH : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH2
  have hlog2 : (4 / 7 : ℝ) < Real.log 2 := BI.log_two_gt
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by rw [hMdef]; linarith)
  have hpi' : 1 / π ≤ 1 / 3 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
    linarith
  rw [sum_intRange_eq ha hab f]
  -- the half-integer endpoints
  set a₁ : ℝ := ⌊a + 1 / 2⌋ + 1 / 2 with ha₁
  set b₁ : ℝ := ⌊b - 1 / 2⌋ + 1 / 2 with hb₁
  have haa₁ : a < a₁ := by
    rw [ha₁]
    have := Int.lt_floor_add_one (a + 1 / 2)
    linarith
  have ha₁a : a₁ ≤ a + 1 := by
    rw [ha₁]
    have := Int.floor_le (a + 1 / 2)
    linarith
  have hb₁b : b₁ ≤ b := by
    rw [hb₁]
    have := Int.floor_le (b - 1 / 2)
    linarith
  have hbb₁ : b - 1 < b₁ := by
    rw [hb₁]
    have := Int.lt_floor_add_one (b - 1 / 2)
    linarith
  have hec : Continuous fun x => e (f x) := continuous_e_comp hf.continuous
  have hfl_a : ⌊a₁⌋ ≤ ⌊a⌋ + 1 := by
    have := Int.floor_le_floor ha₁a
    rw [Int.floor_add_one] at this
    exact this
  have hfl_b : ⌊b⌋ ≤ ⌊b₁⌋ + 1 := by
    have : b ≤ b₁ + 1 := by linarith
    have := Int.floor_le_floor this
    rw [Int.floor_add_one] at this
    exact this
  -- the short-window bound for the main term
  have hshort : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      ‖∑ h ∈ Finset.Icc H₁ H₂, ∫ x in p..q, e (f x - h * x)‖ ≤ 4 + 4 * Real.log M :=
    fun p q hpq hlen => norm_sum_integral_short hf.continuous h12 hpq hlen
  have hconst : 4 + 4 * Real.log M ≤ 4 + 8 * Real.log H := by linarith
  rcases le_or_gt a₁ b₁ with hcase | hcase
  · -- the generic case: `a ≤ a₁ ≤ b₁ ≤ b`
    have hab' : a < b := by linarith
    have hmid := mid_bound hf hab' hanti hH haa₁.le hcase hb₁b ha₁ hb₁
    -- split the sum and the integrals
    have hfl1 : ⌊a⌋ ≤ ⌊a₁⌋ := Int.floor_le_floor haa₁.le
    have hfl2 : ⌊a₁⌋ ≤ ⌊b₁⌋ := Int.floor_le_floor hcase
    have hfl3 : ⌊b₁⌋ ≤ ⌊b⌋ := Int.floor_le_floor hb₁b
    have hsum : ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, e (f n) =
        (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊a₁⌋, e (f n)) + (∑ n ∈ Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, e (f n)) +
          ∑ n ∈ Finset.Ioc ⌊b₁⌋ ⌊b⌋, e (f n) := by
      rw [sum_Ioc_split (fun n : ℤ => e (f n)) hfl1 (hfl2.trans hfl3),
        sum_Ioc_split (fun n : ℤ => e (f n)) hfl2 hfl3]
      ring
    have hint : ∀ (h : ℤ) (p q : ℝ), IntervalIntegrable (fun x => e (f x - h * x)) volume p q :=
      fun h p q => (continuous_e_comp (hf.continuous.sub (continuous_const.mul continuous_id))).intervalIntegrable _ _
    have hmain : ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..b, e (f x - h * x) =
        (∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..a₁, e (f x - h * x)) +
          (∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a₁..b₁, e (f x - h * x)) +
          ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in b₁..b, e (f x - h * x) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [integral_add_adjacent_intervals (hint h a a₁) (hint h a₁ b₁),
        integral_add_adjacent_intervals ((hint h a a₁).trans (hint h a₁ b₁)) (hint h b₁ b)]
    rw [hsum, hmain]
    have hs1 : ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊a₁⌋, e (f n)‖ ≤ 1 :=
      norm_sum_Ioc_le_one (fun x => e (f x)) (fun x => (norm_e_one _).le) hfl_a
    have hs3 : ‖∑ n ∈ Finset.Ioc ⌊b₁⌋ ⌊b⌋, e (f n)‖ ≤ 1 :=
      norm_sum_Ioc_le_one (fun x => e (f x)) (fun x => (norm_e_one _).le) hfl_b
    have hm1 := hshort a a₁ haa₁.le ha₁a
    have hm3 := hshort b₁ b hb₁b (by linarith)
    have hrearr : (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊a₁⌋, e (f n)) + (∑ n ∈ Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, e (f n)) +
          (∑ n ∈ Finset.Ioc ⌊b₁⌋ ⌊b⌋, e (f n)) -
        ((∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..a₁, e (f x - h * x)) +
          (∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a₁..b₁, e (f x - h * x)) +
          ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in b₁..b, e (f x - h * x)) =
        ((∑ n ∈ Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, e (f n)) -
          ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a₁..b₁, e (f x - h * x)) +
        (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊a₁⌋, e (f n)) + (∑ n ∈ Finset.Ioc ⌊b₁⌋ ⌊b⌋, e (f n)) -
        (∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..a₁, e (f x - h * x)) -
        ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in b₁..b, e (f x - h * x) := by ring
    rw [hrearr]
    set A : ℂ := (∑ n ∈ Finset.Ioc ⌊a₁⌋ ⌊b₁⌋, e (f n)) -
      ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a₁..b₁, e (f x - h * x) with hA
    set B : ℂ := ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊a₁⌋, e (f n) with hB
    set C : ℂ := ∑ n ∈ Finset.Ioc ⌊b₁⌋ ⌊b⌋, e (f n) with hC
    set D : ℂ := ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..a₁, e (f x - h * x) with hD
    set E : ℂ := ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in b₁..b, e (f x - h * x) with hE
    have htot : ‖A + B + C - D - E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
      calc ‖A + B + C - D - E‖ ≤ ‖A + B + C - D‖ + ‖E‖ := norm_sub_le _ _
        _ ≤ (‖A + B + C‖ + ‖D‖) + ‖E‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((‖A + B‖ + ‖C‖) + ‖D‖) + ‖E‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖) + ‖E‖ := by gcongr; exact norm_add_le _ _
    refine htot.trans ?_
    have e1 : (2 / π) * Real.log M ≤ (2 / 3) * Real.log M := by
      apply mul_le_mul_of_nonneg_right _ hlogM0
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      linarith
    have e2 : 4 / π ≤ 4 / 3 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      linarith
    linarith
  · -- no half-integer in `[a, b]`: then `b − a < 1`
    have hlen : b < a + 1 := by
      -- `b₁ < a₁` with `a₁ ≤ a + 1` and `b₁ > b − 1` gives `b < a + 2`; sharpen:
      -- `⌊b − 1/2⌋ < ⌊a + 1/2⌋` so `b − 1/2 < ⌊a + 1/2⌋ ≤ a + 1/2`
      have h1 : ⌊b - 1 / 2⌋ < ⌊a + 1 / 2⌋ := by
        by_contra hcon
        push Not at hcon
        have : (⌊a + 1 / 2⌋ : ℝ) ≤ ⌊b - 1 / 2⌋ := by exact_mod_cast hcon
        rw [ha₁, hb₁] at hcase
        linarith
      have h2 : b - 1 / 2 < ⌊a + 1 / 2⌋ := by
        have := Int.floor_le_floor (show b - 1 / 2 ≤ b - 1 / 2 from le_rfl)
        have h3 : (⌊b - 1 / 2⌋ : ℝ) ≤ b - 1 / 2 := Int.floor_le _
        have h4 : ((⌊b - 1 / 2⌋ + 1 : ℤ) : ℝ) ≤ ⌊a + 1 / 2⌋ := by exact_mod_cast h1
        have h5 := Int.lt_floor_add_one (b - 1 / 2)
        push_cast at h4
        linarith
      have h3 : (⌊a + 1 / 2⌋ : ℝ) ≤ a + 1 / 2 := Int.floor_le _
      linarith
    have hfl : ⌊b⌋ ≤ ⌊a⌋ + 1 := by
      have := Int.floor_le_floor hlen.le
      rw [Int.floor_add_one] at this
      exact this
    have hs : ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, e (f n)‖ ≤ 1 :=
      norm_sum_Ioc_le_one (fun x => e (f x)) (fun x => (norm_e_one _).le) hfl
    have hm := hshort a b hab hlen.le
    refine (norm_sub_le _ _).trans ?_
    linarith

end LeanProofs.IntegerPoints
