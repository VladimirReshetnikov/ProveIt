import IntegerPoints.AProcess
import IntegerPoints.ExponentPairs
import IntegerPoints.ExponentPairHalf
import IntegerPoints.WeylVanDerCorput
import IntegerPoints.KuzminLandau
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The A-process for exponent pairs, part II: Graham–Kolesnik Theorem 3.8

If `(k, l)` is an exponent pair then so is
`A(k, l) = (k/(2k+2), (k+l+1)/(2k+2))`.

Proof (Graham–Kolesnik §3.4, adapted to the definition with the `+ y⁻¹N^s`
term).  Write `L = yN^{-s}` and `S = Σ_{a<n≤b} e(f(n))`.

* `N < 1`: the sum has at most one term.
* `N ≥ 1`, `L ≤ 1`: the pair `(1/2, 1/2)` gives `|S| ≪ L^{1/2}N^{1/2} + L⁻¹`,
  and `L^{1/2} ≤ L^κ`, `N^{1/2} ≤ N^λ`.
* `N ≥ 1`, `1 < L < 1 + log N`: the pair `(1/2, 1/2)` gives
  `|S| ≪ (N^{1/3})^{1/2} N^{1/2} + L⁻¹ ≪ N^{2/3} + L⁻¹ ≪ L^κ N^λ + L⁻¹`.
* `N ≥ 1`, `L ≥ 1 + log N`: Weyl differencing (Zhai–Cao Lemma 4) with
  shift length `Q`, Lemma 3.7 and the pair `(k, l)` for `s + 1` give
  `|S|² ≪ N²/Q + Q^k L^k N^{l-k+1}`.  With `Q₀ = N^{(1+k-l)/(k+1)} L^{-k/(k+1)}`
  the two terms balance and `N²/Q₀ = (L^κ N^λ)²`; if `Q₀ < 1` the trivial
  bound `|S| ≤ 3N < 3L^κN^λ` applies, and if `Q₀` exceeds the admissible
  range `Q ≤ cN` then `|S|² ≪ N²/(cN)`, i.e. `|S| ≪ N^{1/2} ≤ L^κ N^λ`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace AP

/-! ### Monotonicity of the class -/

theorem InGKClass.mono {N : ℝ} {P P' : ℕ} {s y ε ε' a b : ℝ} {f : ℝ → ℝ}
    (hε0 : 0 < ε) (hP : P' ≤ P) (hεε : ε ≤ ε') (hf : InGKClass N P s y ε a b f) :
    InGKClass N P' s y ε' a b f := by
  obtain ⟨h1, h2, h3, hcd, hcond⟩ := hf
  refine ⟨h1, h2, h3, hcd.of_le (by exact_mod_cast hP), fun p hp t ht => ?_⟩
  have this := hcond p (by omega) t ht
  have hpos : 0 < ε * (∏ i ∈ range p, (s + i)) * y * t ^ (-s - p) :=
    lt_of_le_of_lt (abs_nonneg _) this
  have hX : 0 < (∏ i ∈ range p, (s + i)) * y * t ^ (-s - p) := by
    by_contra hX
    push Not at hX
    nlinarith
  calc _ < ε * (∏ i ∈ range p, (s + i)) * y * t ^ (-s - p) := this
    _ ≤ ε' * (∏ i ∈ range p, (s + i)) * y * t ^ (-s - p) := by nlinarith

/-! ### The harmonic sum -/

theorem sum_inv_succ_le (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℝ)⁻¹ := by
    rw [harmonic, Rat.cast_sum]
    simp
  rwa [e] at h

/-! ### Weyl differencing for `Σ e(f(n))` -/

/-- The correlation sum of the indicator-weighted `e(f n)` is `S₁(q)`. -/
theorem corr_eq {a b : ℝ} (f : ℝ → ℝ) (hb : 0 ≤ b) (hba : b ≤ 3 * a) (q : ℕ) :
    ∑ n ∈ intRange a (3 * a - q),
        (if n ∈ intRange a b then e (f n) else 0) *
          starRingEnd ℂ (if n + q ∈ intRange a b then e (f ((n + q : ℕ) : ℝ)) else 0) =
      ∑ n ∈ intRange a (b - q), e (f n - f (n + q)) := by
  classical
  have hfl : ⌊b⌋₊ ≤ ⌊3 * a⌋₊ := Nat.floor_le_floor hba
  have hterm : ∀ n : ℕ, (if n ∈ intRange a b then e (f n) else 0) *
      starRingEnd ℂ (if n + q ∈ intRange a b then e (f ((n + q : ℕ) : ℝ)) else 0) =
      if n ∈ intRange a b ∧ n + q ∈ intRange a b then e (f n - f (n + q)) else 0 := by
    intro n
    by_cases h1 : n ∈ intRange a b <;> by_cases h2 : n + q ∈ intRange a b <;>
      simp [h1, h2, sub_eq_add_neg, KL.e_add, KL.e_neg]
  simp_rw [hterm]
  rw [intRange_sub_eq_filter a (3 * a) (by linarith) q, intRange_sub_eq_filter a b hb q,
    Finset.sum_filter, Finset.sum_filter]
  symm
  rw [← Finset.sum_subset (Finset.Ioc_subset_Ioc_right hfl) ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h : n + q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊
    · rw [if_pos h, if_pos (Finset.Ioc_subset_Ioc_right hfl h), if_pos ⟨hn, h⟩]
    · rw [if_neg h]
      by_cases h' : n + q ∈ Finset.Ioc ⌊a⌋₊ ⌊3 * a⌋₊
      · rw [if_pos h', if_neg (fun hh => h hh.2)]
      · rw [if_neg h']
  · intro n _ hn
    by_cases h1 : n + q ∈ Finset.Ioc ⌊a⌋₊ ⌊3 * a⌋₊
    · rw [if_pos h1, if_neg (fun hh => hn hh.1)]
    · rw [if_neg h1]

/-- Weyl differencing for `S = Σ_{a<n≤b} e(f n)`, `[a, b] ⊆ [N, 2N]`, `N ≥ 1`, `1 ≤ Q ≤ N`:
`‖S‖² ≤ |CW| (2N/Q) Σ_{q ≤ Q} ‖S₁(q)‖`, where `S₁(q) = Σ_{a<n≤b-q} e(f n - f(n+q))`. -/
theorem weyl_step (CW : ℝ)
    (hCW : ∀ (N Q : ℝ) (a : ℕ → ℂ), 1 ≤ Q → Q ≤ N →
      ‖∑ n ∈ intRange N (3 * N), a n‖ ^ 2 ≤
        CW * (N / Q) * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1),
          (1 - q / Q) * (∑ n ∈ intRange N (3 * N - q), a n * starRingEnd ℂ (a (n + q))).re)
    {N a b Q : ℝ} (f : ℝ → ℝ) (hN : 1 ≤ N) (hNa : N ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * N)
    (hQ1 : 1 ≤ Q) (hQN : Q ≤ N) :
    ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
      |CW| * (2 * N / Q) * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1),
        ‖∑ n ∈ intRange a (b - q), e (f n - f (n + q))‖ := by
  classical
  have h1 : ∑ n ∈ intRange a (3 * a), (if n ∈ intRange a b then e (f n) else 0) =
      ∑ n ∈ intRange a b, e (f n) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, intRange, Finset.mem_Ioc]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      exact ⟨⟨h.1, le_trans h.2 (Nat.floor_le_floor (by linarith))⟩, h⟩
  have hmain := hCW a Q (fun n => if n ∈ intRange a b then e (f n) else 0) hQ1 (hQN.trans hNa)
  beta_reduce at hmain
  rw [h1] at hmain
  refine hmain.trans ?_
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 ≤ a / Q := div_nonneg (by linarith) hQ0.le
  set S0 := ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), (1 - q / Q) *
      (∑ n ∈ intRange a (3 * a - q), (if n ∈ intRange a b then e (f n) else 0) *
        starRingEnd ℂ (if n + q ∈ intRange a b then e (f ((n + q : ℕ) : ℝ)) else 0)).re
    with hS0def
  set T := ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), ‖∑ n ∈ intRange a (b - q), e (f n - f (n + q))‖
    with hTdef
  have hsum : |S0| ≤ T := by
    rw [hS0def, hTdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    rw [corr_eq f (by linarith) (by linarith) q, abs_mul]
    have hq : (q : ℝ) ≤ Q := by
      rw [Finset.mem_range] at hq
      have : q ≤ ⌊Q⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hQ0.le)
    have h0 : 0 ≤ (q : ℝ) / Q := by positivity
    have h1' : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact hq
    have h01 : |1 - (q : ℝ) / Q| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |1 - (q : ℝ) / Q| * |(∑ n ∈ intRange a (b - q), e (f n - f (n + q))).re|
        ≤ 1 * ‖∑ n ∈ intRange a (b - q), e (f n - f (n + q))‖ :=
          mul_le_mul h01 (Complex.abs_re_le_norm _) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc CW * (a / Q) * S0 ≤ |CW * (a / Q) * S0| := le_abs_self _
    _ = |CW| * (a / Q) * |S0| := by rw [abs_mul, abs_mul, abs_of_nonneg hX0]
    _ ≤ |CW| * (2 * N / Q) * T := by
        apply mul_le_mul _ hsum (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) (div_nonneg (by linarith) hQ0.le))
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hQ0.le) (abs_nonneg _)

/-! ### The bound for `S₁(q)` -/

/-- For `1 ≤ q < ε₁N/(s+P+1)`: `‖S₁(q)‖ ≤ C ((sqy N^{-s-1})^k N^l + (sqy)⁻¹ N^{s+1})`. -/
theorem diff_sum_bound {N : ℝ} {P : ℕ} {s y ε ε₁ a b Ckl k l : ℝ} {f : ℝ → ℝ}
    (hs : 0 < s) (hy : 0 < y) (hε₁ : 0 < ε₁) (h3 : 3 * ε₁ ≤ ε) (hN : 0 < N)
    (hf : InGKClass N (P + 1) s y ε₁ a b f)
    (hbound : ∀ (N y a b : ℝ) (g : ℝ → ℝ), 0 < N → 0 < y → InGKClass N P (s + 1) y ε a b g →
      ‖∑ n ∈ intRange a b, e (g n)‖ ≤
        Ckl * ((y * N ^ (-(s + 1))) ^ k * N ^ l + y⁻¹ * N ^ (s + 1)))
    (q : ℕ) (hq1 : 1 ≤ q) (hqε : (q : ℝ) < ε₁ * N / (s + P + 1)) :
    ‖∑ n ∈ intRange a (b - q), e (f n - f (n + q))‖ ≤
      max Ckl 0 * ((s * q * y * N ^ (-(s + 1))) ^ k * N ^ l + (s * q * y)⁻¹ * N ^ (s + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hX : 0 ≤ (s * q * y * N ^ (-(s + 1))) ^ k * N ^ l + (s * q * y)⁻¹ * N ^ (s + 1) := by
    positivity
  rcases le_or_gt (q : ℝ) (b - a) with hqb | hqb
  · have h37 := lemma37 hs hy hε₁ hf hq0 hqb hqε
    have h37' : InGKClass N P (s + 1) (s * q * y) ε a (b - q) (fun x => f x - f (x + q)) :=
      InGKClass.mono (by positivity) le_rfl h3 h37
    have := hbound N (s * q * y) a (b - q) _ hN (by positivity) h37'
    calc ‖∑ n ∈ intRange a (b - q), e (f n - f (n + q))‖
        ≤ Ckl * ((s * q * y * N ^ (-(s + 1))) ^ k * N ^ l + (s * q * y)⁻¹ * N ^ (s + 1)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  · have hempty : intRange a (b - q) = ∅ := by
      rw [intRange, Finset.Ioc_eq_empty_of_le]
      exact Nat.floor_le_floor (by linarith)
    rw [hempty, Finset.sum_empty, norm_zero]
    exact mul_nonneg (le_max_right _ _) hX

/-! ### The Weyl bound `‖S‖² ≪ N²/Q + Q^k L^k N^{l-k+1}` -/

theorem weyl_bound {N a b Q s y ε ε₁ L CW Ckl k l : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hs : 0 < s) (hy : 0 < y) (hε₁ : 0 < ε₁) (h3 : 3 * ε₁ ≤ ε) (hN : 1 ≤ N)
    (hf : InGKClass N (P + 1) s y ε₁ a b f)
    (hCW : ∀ (N Q : ℝ) (a : ℕ → ℂ), 1 ≤ Q → Q ≤ N →
      ‖∑ n ∈ intRange N (3 * N), a n‖ ^ 2 ≤
        CW * (N / Q) * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1),
          (1 - q / Q) * (∑ n ∈ intRange N (3 * N - q), a n * starRingEnd ℂ (a (n + q))).re)
    (hbound : ∀ (N y a b : ℝ) (g : ℝ → ℝ), 0 < N → 0 < y → InGKClass N P (s + 1) y ε a b g →
      ‖∑ n ∈ intRange a b, e (g n)‖ ≤
        Ckl * ((y * N ^ (-(s + 1))) ^ k * N ^ l + y⁻¹ * N ^ (s + 1)))
    (hk : 0 ≤ k) (hL : L = y * N ^ (-s)) (hLlog : 1 + Real.log N ≤ L)
    (hQ1 : 1 ≤ Q) (hQN : Q ≤ N) (hQε : Q < ε₁ * N / (s + P + 1)) :
    ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
      (6 * |CW| + 2 * |CW| * max Ckl 0 * s⁻¹ + 2 * |CW| * max Ckl 0 * s ^ k) *
        (N ^ 2 / Q + Q ^ k * L ^ k * N ^ (l - k + 1)) := by
  have hf' := hf
  obtain ⟨hNa, hab, hb2N, -, -⟩ := hf'
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < L := by rw [hL]; positivity
  have hQ0 : 0 < Q := by linarith
  set Ck := max Ckl 0 with hCk
  have hCk0 : 0 ≤ Ck := le_max_right _ _
  -- Weyl differencing
  have hW := weyl_step CW hCW f hN hNa hab hb2N hQ1 hQN
  -- the `q = 0` term
  have hS0 : ‖∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)), e (f n - f (n + ((0 : ℕ) : ℝ)))‖ ≤ 3 * N := by
    calc ‖∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)), e (f n - f (n + ((0 : ℕ) : ℝ)))‖
        ≤ ∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)), ‖e (f n - f (n + ((0 : ℕ) : ℝ)))‖ :=
          norm_sum_le _ _
      _ = (intRange a b).card := by simp [norm_e]
      _ ≤ 3 * N := card_intRange_le hN0 hNa hab hb2N
  -- the terms `q ≥ 1`
  have hQfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hQfl1 : 1 ≤ ⌊Q⌋₊ := (Nat.one_le_floor_iff _).2 hQ1
  have hterm : ∀ i ∈ Finset.range ⌊Q⌋₊,
      ‖∑ n ∈ intRange a (b - ((i + 1 : ℕ) : ℝ)), e (f n - f (n + ((i + 1 : ℕ) : ℝ)))‖ ≤
        Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l +
          Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ * ((i + 1 : ℕ) : ℝ)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiQ : ((i + 1 : ℕ) : ℝ) ≤ Q := by
      have : i + 1 ≤ ⌊Q⌋₊ := by omega
      exact le_trans (by exact_mod_cast this) hQfl
    have hq1 : 1 ≤ i + 1 := by omega
    have hi0 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast hq1
    have := diff_sum_bound hs hy hε₁ h3 hN0 hf hbound (i + 1) hq1 (lt_of_le_of_lt hiQ hQε)
    refine this.trans ?_
    have hpow : (s * ((i + 1 : ℕ) : ℝ) * y * N ^ (-(s + 1))) ^ k ≤
        (s * Q * y * N ^ (-(s + 1))) ^ k := by
      apply Real.rpow_le_rpow (by positivity) _ hk
      have : 0 ≤ y * N ^ (-(s + 1)) := by positivity
      calc s * ((i + 1 : ℕ) : ℝ) * y * N ^ (-(s + 1))
          = s * ((i + 1 : ℕ) : ℝ) * (y * N ^ (-(s + 1))) := by ring
        _ ≤ s * Q * (y * N ^ (-(s + 1))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hiQ hs.le) this
        _ = s * Q * y * N ^ (-(s + 1)) := by ring
    have e1 : (s * ((i + 1 : ℕ) : ℝ) * y)⁻¹ * N ^ (s + 1) =
        (y⁻¹ * N ^ (s + 1)) * s⁻¹ * ((i + 1 : ℕ) : ℝ)⁻¹ := by
      field_simp
    rw [mul_add, e1]
    have : 0 ≤ N ^ l := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpow this, hCk0]
  -- sum the terms
  have hsum1 : ∑ i ∈ Finset.range ⌊Q⌋₊,
      ‖∑ n ∈ intRange a (b - ((i + 1 : ℕ) : ℝ)), e (f n - f (n + ((i + 1 : ℕ) : ℝ)))‖ ≤
        Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l * Q +
          Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ * (1 + Real.log N) := by
    calc ∑ i ∈ Finset.range ⌊Q⌋₊,
          ‖∑ n ∈ intRange a (b - ((i + 1 : ℕ) : ℝ)), e (f n - f (n + ((i + 1 : ℕ) : ℝ)))‖
        ≤ ∑ i ∈ Finset.range ⌊Q⌋₊, (Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l +
            Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ * ((i + 1 : ℕ) : ℝ)⁻¹) := Finset.sum_le_sum hterm
      _ = ⌊Q⌋₊ * (Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l) +
            Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ * ∑ i ∈ Finset.range ⌊Q⌋₊, ((i + 1 : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Finset.mul_sum]
      _ ≤ Q * (Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l) +
            Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ * (1 + Real.log N) := by
          have hlog : Real.log ⌊Q⌋₊ ≤ Real.log N :=
            Real.log_le_log (by exact_mod_cast hQfl1) (hQfl.trans hQN)
          have hh := (sum_inv_succ_le ⌊Q⌋₊).trans (by linarith : 1 + Real.log ⌊Q⌋₊ ≤ 1 + Real.log N)
          have h1 : 0 ≤ Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l := by positivity
          have h2 : 0 ≤ Ck * (y⁻¹ * N ^ (s + 1)) * s⁻¹ := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_right hQfl h1) (mul_le_mul_of_nonneg_left hh h2)
      _ = _ := by ring
  -- rewrite in terms of `L`
  have hyN : y * N ^ (-(s + 1)) = L / N := by
    rw [hL, show -(s + 1) = -s - 1 by ring, Real.rpow_sub_one hN0.ne', mul_div_assoc]
  have hNy : y⁻¹ * N ^ (s + 1) = N / L := by
    rw [hL, Real.rpow_neg hN0.le, Real.rpow_add_one hN0.ne']
    field_simp
  have hNk : N ^ k ≠ 0 := (Real.rpow_pos_of_pos hN0 k).ne'
  have hkey : (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l * Q * (N / Q) =
      s ^ k * (Q ^ k * L ^ k * N ^ (l - k + 1)) := by
    rw [show s * Q * y * N ^ (-(s + 1)) = s * Q * (y * N ^ (-(s + 1))) by ring, hyN,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hs.le hQ0.le,
      Real.div_rpow hL0.le hN0.le, Real.rpow_add_one hN0.ne', Real.rpow_sub hN0]
    field_simp
  have hlogL : (N / L) * s⁻¹ * (1 + Real.log N) ≤ N * s⁻¹ := by
    have : (N / L) * s⁻¹ * (1 + Real.log N) ≤ (N / L) * s⁻¹ * L :=
      mul_le_mul_of_nonneg_left hLlog (by positivity)
    rw [show (N / L) * s⁻¹ * L = N * s⁻¹ by field_simp] at this
    exact this
  -- assemble
  rw [Finset.sum_range_succ'] at hW
  set T₁ := Q ^ k * L ^ k * N ^ (l - k + 1) with hT₁
  have hT : ∑ i ∈ Finset.range ⌊Q⌋₊,
        ‖∑ n ∈ intRange a (b - ((i + 1 : ℕ) : ℝ)), e (f n - f (n + ((i + 1 : ℕ) : ℝ)))‖ +
      ‖∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)), e (f n - f (n + ((0 : ℕ) : ℝ)))‖ ≤
      Ck * s ^ k * T₁ * (Q / N) + Ck * (N * s⁻¹) + 3 * N := by
    have := hsum1
    rw [hNy] at this
    have h' : Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l * Q = Ck * s ^ k * T₁ * (Q / N) := by
      have e2 : (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l * Q = s ^ k * T₁ * (Q / N) := by
        rw [hT₁, ← hkey]
        field_simp
      rw [show Ck * s ^ k * T₁ * (Q / N) = Ck * (s ^ k * T₁ * (Q / N)) by ring, ← e2]
      ring
    have h'' : Ck * (N / L) * s⁻¹ * (1 + Real.log N) ≤ Ck * (N * s⁻¹) := by
      have := mul_le_mul_of_nonneg_left hlogL hCk0
      rw [show Ck * ((N / L) * s⁻¹ * (1 + Real.log N)) = Ck * (N / L) * s⁻¹ * (1 + Real.log N) by
        ring] at this
      exact this
    calc ∑ i ∈ Finset.range ⌊Q⌋₊,
          ‖∑ n ∈ intRange a (b - ((i + 1 : ℕ) : ℝ)), e (f n - f (n + ((i + 1 : ℕ) : ℝ)))‖ +
        ‖∑ n ∈ intRange a (b - ((0 : ℕ) : ℝ)), e (f n - f (n + ((0 : ℕ) : ℝ)))‖
        ≤ (Ck * (s * Q * y * N ^ (-(s + 1))) ^ k * N ^ l * Q +
            Ck * (N / L) * s⁻¹ * (1 + Real.log N)) + 3 * N := add_le_add this hS0
      _ = Ck * s ^ k * T₁ * (Q / N) + Ck * (N / L) * s⁻¹ * (1 + Real.log N) + 3 * N := by
          rw [h']
      _ ≤ Ck * s ^ k * T₁ * (Q / N) + Ck * (N * s⁻¹) + 3 * N := by linarith
  have hC0 : 0 ≤ |CW| * (2 * N / Q) := by positivity
  have ht1 : 0 ≤ T₁ := by positivity
  have ht2 : 0 ≤ N ^ 2 / Q := by positivity
  have hsinv : 0 ≤ s⁻¹ := by positivity
  have hsk : 0 ≤ s ^ k := by positivity
  calc ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤ _ := hW
    _ ≤ |CW| * (2 * N / Q) * (Ck * s ^ k * T₁ * (Q / N) + Ck * (N * s⁻¹) + 3 * N) :=
        mul_le_mul_of_nonneg_left hT hC0
    _ = 6 * |CW| * (N ^ 2 / Q) + 2 * |CW| * Ck * s⁻¹ * (N ^ 2 / Q) +
          2 * |CW| * Ck * s ^ k * T₁ := by
        field_simp
        ring
    _ ≤ _ := by
        have h0 := mul_nonneg (abs_nonneg CW) ht1
        have h1 := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg CW) hCk0) hsinv) ht1
        have h2 := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg CW) hCk0) hsk) ht2
        nlinarith

/-! ### The A-process -/

set_option maxHeartbeats 1000000 in
/-- **Graham–Kolesnik, Theorem 3.8** (the A-process).  If `(k, l)` is an exponent pair,
so is `A(k, l) = (k/(2k+2), (k+l+1)/(2k+2))`. -/
theorem isExponentPair_A {k l : ℝ} (h : IsExponentPair k l) :
    IsExponentPair (k / (2 * k + 2)) ((k + l + 1) / (2 * k + 2)) := by
  obtain ⟨hk0, hk1, hl0, hl1, hkl⟩ := h
  obtain ⟨-, -, -, -, hhalf⟩ := isExponentPair_half_half
  obtain ⟨CW, hCW⟩ := zhaiCao_lemma4_holds 3 (by norm_num)
  have h2k : 0 < 2 * k + 2 := by linarith
  set κ := k / (2 * k + 2) with hκ
  set lam := (k + l + 1) / (2 * k + 2) with hlam
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 / 2 := by rw [hκ, div_le_iff₀ h2k]; linarith
  have hlam0 : 1 / 2 ≤ lam := by rw [hlam, le_div_iff₀ h2k]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_iff₀ h2k]; linarith
  have hlam23 : 2 / 3 ≤ lam := by rw [hlam, le_div_iff₀ h2k]; linarith
  clear_value κ lam
  refine ⟨hκ0, hκ1, hlam0, hlam1, fun s hs => ?_⟩
  obtain ⟨P, ε, Ckl, hε0, hε1, hbound⟩ := hkl (s + 1) (by linarith)
  obtain ⟨P₂, ε₂, C₂, hε₂0, hε₂1, hbound₂⟩ := hhalf s hs
  set P₁ := max (P + 1) P₂ with hP₁
  set ε₁ := min (ε / 3) ε₂ with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by linarith) hε₂0
  have hε₁ε : 3 * ε₁ ≤ ε := by
    have := min_le_left (ε / 3) ε₂
    linarith
  have hε₁₂ : ε₁ ≤ ε₂ := min_le_right _ _
  have hε₁half : ε₁ < 1 / 2 := lt_of_le_of_lt hε₁₂ hε₂1
  set Ck := max Ckl 0 with hCk
  have hCk0 : 0 ≤ Ck := le_max_right _ _
  set C₂' := max C₂ 0 with hC₂'
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  set C₁ := 6 * |CW| + 2 * |CW| * Ck * s⁻¹ + 2 * |CW| * Ck * s ^ k with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  set cε := ε₁ / (2 * (s + P + 1)) with hcε
  have hcε0 : 0 < cε := by positivity
  have hcε1 : cε < 1 := by
    rw [hcε, div_lt_one (by positivity)]
    linarith
  set Cf := 2 + 2 * C₂' + 3 + Real.sqrt (2 * C₁) + 3 / Real.sqrt cε + Real.sqrt (2 * C₁ / cε)
    with hCf
  have ht1 : 0 ≤ Real.sqrt (2 * C₁) := Real.sqrt_nonneg _
  have ht2 : 0 ≤ 3 / Real.sqrt cε := by positivity
  have ht3 : 0 ≤ Real.sqrt (2 * C₁ / cε) := Real.sqrt_nonneg _
  refine ⟨P₁, ε₁, Cf, hε₁0, hε₁half, fun N y a b f hN hy hf => ?_⟩
  have hf' := hf
  obtain ⟨hNa, hab, hb2N, -, -⟩ := hf'
  -- notation
  set L := y * N ^ (-s) with hL
  have hL0 : 0 < L := by positivity
  set X := L ^ κ * N ^ lam + y⁻¹ * N ^ s with hX
  have hX0 : 0 ≤ X := by positivity
  have hLinv : y⁻¹ * N ^ s = L⁻¹ := by
    rw [hL, mul_inv, Real.rpow_neg hN.le, inv_inv]
  have hXL : L⁻¹ ≤ X := by
    rw [hX, ← hLinv]
    have : 0 ≤ L ^ κ * N ^ lam := by positivity
    linarith
  have hXmain : L ^ κ * N ^ lam ≤ X := by
    rw [hX]
    have : 0 ≤ y⁻¹ * N ^ s := by positivity
    linarith
  have hP₁a : P + 1 ≤ P₁ := le_max_left _ _
  have hP₁b : P₂ ≤ P₁ := le_max_right _ _
  clear_value L X
  have hS3N : ‖∑ n ∈ intRange a b, e (f n)‖ ≤ 3 * N := by
    calc ‖∑ n ∈ intRange a b, e (f n)‖ ≤ ∑ n ∈ intRange a b, ‖e (f n)‖ := norm_sum_le _ _
      _ = (intRange a b).card := by simp [norm_e]
      _ ≤ 3 * N := card_intRange_le hN hNa hab hb2N
  -- it suffices to find a constant `c ≤ Cf` for each case
  suffices hsuff : ∃ c : ℝ, c ≤ Cf ∧ ‖∑ n ∈ intRange a b, e (f n)‖ ≤ c * X by
    obtain ⟨c, hc, hSc⟩ := hsuff
    exact hSc.trans (mul_le_mul_of_nonneg_right hc hX0)
  rcases lt_or_ge N 1 with hN1 | hN1
  · -- Case A: `N < 1`, at most one term
    refine ⟨2, by linarith, ?_⟩
    have hS1 : ‖∑ n ∈ intRange a b, e (f n)‖ ≤ ((intRange a b).card : ℝ) := by
      calc _ ≤ ∑ n ∈ intRange a b, ‖e (f n)‖ := norm_sum_le _ _
        _ = _ := by simp [norm_e]
    have hcard : (intRange a b).card ≤ 1 := by
      rw [intRange, Nat.card_Ioc]
      have : ⌊b⌋₊ < 2 := (Nat.floor_lt (by linarith)).2 (by push_cast; linarith)
      omega
    rcases Nat.eq_zero_or_pos (intRange a b).card with hc0 | hcpos
    · rw [hc0, Nat.cast_zero] at hS1
      linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX0]
    · have hb1 : (1 : ℝ) ≤ b := by
        rw [intRange, Nat.card_Ioc] at hcpos
        have : 1 ≤ ⌊b⌋₊ := by omega
        exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
      have hXhalf : 1 / 2 ≤ X := by
        rcases le_or_gt 1 L with hL1 | hL1
        · have h1 : 1 ≤ L ^ κ := Real.one_le_rpow hL1 hκ0
          have h2 : N ≤ N ^ lam := by
            calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
              _ ≤ N ^ lam := Real.rpow_le_rpow_of_exponent_ge hN hN1.le hlam1
          have h3 : 0 ≤ N ^ lam := by positivity
          have h4 : L ^ κ * N ^ lam ≥ 1 * N ^ lam := mul_le_mul_of_nonneg_right h1 h3
          linarith
        · have : 1 < L⁻¹ := (one_lt_inv₀ hL0).2 hL1
          linarith
      have : ((intRange a b).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith
  -- from now on `N ≥ 1`
  have hf₂ : InGKClass N P₂ s y ε₂ a b f := InGKClass.mono hε₁0 hP₁b hε₁₂ hf
  have hf₁ : InGKClass N (P + 1) s y ε₁ a b f := InGKClass.mono hε₁0 hP₁a le_rfl hf
  have hhalfb : ‖∑ n ∈ intRange a b, e (f n)‖ ≤
      C₂' * (L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹) := by
    have := hbound₂ N y a b f hN hy hf₂
    rw [← hL, hLinv] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hN12 : N ^ (1 / 2 : ℝ) ≤ N ^ lam := Real.rpow_le_rpow_of_exponent_le hN1 hlam0
  rcases le_or_gt L 1 with hL1 | hL1
  · -- Case B: `L ≤ 1`
    refine ⟨C₂', by linarith, ?_⟩
    have h1 : L ^ (1 / 2 : ℝ) ≤ L ^ κ := Real.rpow_le_rpow_of_exponent_ge hL0 hL1 hκ1
    have h2 : L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤ L ^ κ * N ^ lam :=
      mul_le_mul h1 hN12 (by positivity) (by positivity)
    calc _ ≤ C₂' * (L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹) := hhalfb
      _ ≤ C₂' * X := by
          apply mul_le_mul_of_nonneg_left _ hC₂'0
          rw [hX, ← hLinv]
          linarith
  have hLκ : 1 ≤ L ^ κ := Real.one_le_rpow hL1.le hκ0
  have hN23 : N ^ (2 / 3 : ℝ) ≤ L ^ κ * N ^ lam := by
    calc N ^ (2 / 3 : ℝ) ≤ N ^ lam := Real.rpow_le_rpow_of_exponent_le hN1 hlam23
      _ = 1 * N ^ lam := (one_mul _).symm
      _ ≤ L ^ κ * N ^ lam := mul_le_mul_of_nonneg_right hLκ (by positivity)
  rcases lt_or_ge L (1 + Real.log N) with hLlog | hLlog
  · -- Case C: `1 < L < 1 + log N`
    refine ⟨2 * C₂', by linarith, ?_⟩
    have hN13 : 0 < N ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hN _
    have hlog : Real.log N ≤ 3 * N ^ (1 / 3 : ℝ) - 3 := by
      have := Real.log_le_sub_one_of_pos hN13
      rw [Real.log_rpow hN] at this
      linarith
    have hL4 : L ≤ 4 * N ^ (1 / 3 : ℝ) := by linarith
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hL12 : L ^ (1 / 2 : ℝ) ≤ 2 * N ^ (1 / 6 : ℝ) := by
      calc L ^ (1 / 2 : ℝ) ≤ (4 * N ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hL0.le hL4 (by norm_num)
        _ = 2 * N ^ (1 / 6 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hN13.le, h4, ← Real.rpow_mul hN.le]
            norm_num
    have hprod : L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤ 2 * (L ^ κ * N ^ lam) := by
      calc L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤ 2 * N ^ (1 / 6 : ℝ) * N ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hL12 (by positivity)
        _ = 2 * N ^ (2 / 3 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hN]
            norm_num
        _ ≤ 2 * (L ^ κ * N ^ lam) := mul_le_mul_of_nonneg_left hN23 (by norm_num)
    calc _ ≤ C₂' * (L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹) := hhalfb
      _ ≤ C₂' * (2 * (L ^ κ * N ^ lam) + 2 * L⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hC₂'0
          have : 0 ≤ L⁻¹ := by positivity
          linarith
      _ = 2 * C₂' * X := by rw [hX, ← hLinv]; ring
  -- Case D: `L ≥ 1 + log N`: Weyl differencing
  have hwb := fun (Q : ℝ) (hQ1 : 1 ≤ Q) (hQN : Q ≤ N) (hQε : Q < ε₁ * N / (s + P + 1)) =>
    weyl_bound hs hy hε₁0 hε₁ε hN1 hf₁ hCW hbound hk0 hL hLlog hQ1 hQN hQε
  clear hCW hbound hbound₂ hkl hhalf
  have hcεN : ∀ Q : ℝ, Q ≤ cε * N → Q < ε₁ * N / (s + P + 1) := by
    intro Q hQ
    have h1 : cε * N < ε₁ * N / (s + P + 1) := by
      have hpos : 0 < ε₁ * N / (s + P + 1) := by positivity
      rw [hcε, show ε₁ / (2 * (s + P + 1)) * N = (ε₁ * N / (s + P + 1)) / 2 by
        first | (field_simp; done) | (field_simp; ring)]
      linarith
    linarith
  have hk1' : 0 < k + 1 := by linarith
  set α₀ := (1 + k - l) / (k + 1) with hα₀
  set β₀ := -k / (k + 1) with hβ₀
  set Q₀ := N ^ α₀ * L ^ β₀ with hQ₀
  have hQ₀0 : 0 < Q₀ := by positivity
  clear_value Q₀ α₀ β₀
  -- Claim A: `Q₀^k L^k N^{l-k+1} = N²/Q₀`
  have hQ₀k1 : Q₀ ^ (k + 1) = N ^ (1 + k - l) * L ^ (-k) := by
    rw [hQ₀, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN.le,
      ← Real.rpow_mul hL0.le]
    congr 2
    · rw [hα₀]; field_simp
    · rw [hβ₀]; field_simp
  have hA : Q₀ ^ k * L ^ k * N ^ (l - k + 1) = N ^ 2 / Q₀ := by
    rw [eq_div_iff hQ₀0.ne']
    have e1 : Q₀ ^ k * Q₀ = Q₀ ^ (k + 1) := (Real.rpow_add_one hQ₀0.ne' k).symm
    have e2 : L ^ (-k) * L ^ k = 1 := by rw [← Real.rpow_add hL0]; simp
    have e3 : N ^ (1 + k - l) * N ^ (l - k + 1) = N ^ 2 := by
      rw [← Real.rpow_add hN, show (1 + k - l) + (l - k + 1) = (2 : ℝ) by ring, Real.rpow_two]
    calc Q₀ ^ k * L ^ k * N ^ (l - k + 1) * Q₀ = (Q₀ ^ k * Q₀) * L ^ k * N ^ (l - k + 1) := by ring
      _ = (N ^ (1 + k - l) * L ^ (-k)) * L ^ k * N ^ (l - k + 1) := by rw [e1, hQ₀k1]
      _ = (N ^ (1 + k - l) * N ^ (l - k + 1)) * (L ^ (-k) * L ^ k) := by ring
      _ = N ^ 2 := by rw [e2, e3, mul_one]
  -- Claim B: `N²/Q₀ = (L^κ N^lam)²`
  have hB : N ^ 2 / Q₀ = (L ^ κ * N ^ lam) ^ 2 := by
    rw [div_eq_iff hQ₀0.ne', hQ₀, mul_pow, ← Real.rpow_natCast (L ^ κ) 2,
      ← Real.rpow_natCast (N ^ lam) 2, ← Real.rpow_mul hL0.le, ← Real.rpow_mul hN.le]
    push_cast
    rw [show L ^ (κ * 2) * N ^ (lam * 2) * (N ^ α₀ * L ^ β₀) =
        (L ^ (κ * 2) * L ^ β₀) * (N ^ (lam * 2) * N ^ α₀) by ring,
      ← Real.rpow_add hL0, ← Real.rpow_add hN]
    have e1 : κ * 2 + β₀ = 0 := by rw [hκ, hβ₀]; field_simp; ring
    have e2 : lam * 2 + α₀ = 2 := by rw [hlam, hα₀]; field_simp; ring
    rw [e1, e2, Real.rpow_zero, one_mul, Real.rpow_two]
  have hmain0 : 0 ≤ L ^ κ * N ^ lam := by positivity
  -- from `‖S‖² ≤ c² (L^κ N^lam)²` to `‖S‖ ≤ c L^κ N^lam`
  have hsq : ∀ c : ℝ, 0 ≤ c → ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤ c ^ 2 * (L ^ κ * N ^ lam) ^ 2 →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤ c * (L ^ κ * N ^ lam) := by
    intro c hc hle
    rw [← mul_pow] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
  rcases lt_or_ge Q₀ 1 with hQ₀1 | hQ₀1
  · -- (i) `Q₀ < 1`: trivial bound
    refine ⟨3, by linarith, ?_⟩
    have h1 : N ^ 2 < (L ^ κ * N ^ lam) ^ 2 := by
      have hN2 : 0 < N ^ 2 := by positivity
      calc N ^ 2 = N ^ 2 * 1 := (mul_one _).symm
        _ < N ^ 2 / Q₀ := by
            rw [lt_div_iff₀ hQ₀0]
            nlinarith
        _ = (L ^ κ * N ^ lam) ^ 2 := hB
    have h2 : N < L ^ κ * N ^ lam := lt_of_pow_lt_pow_left₀ 2 hmain0 h1
    calc _ ≤ 3 * N := hS3N
      _ ≤ 3 * (L ^ κ * N ^ lam) := by linarith
      _ ≤ 3 * X := by linarith
  rcases le_or_gt Q₀ (cε * N) with hQ₀c | hQ₀c
  · -- (ii) `1 ≤ Q₀ ≤ cε N`: `Q = Q₀`
    refine ⟨Real.sqrt (2 * C₁), by linarith, ?_⟩
    have hw := hwb Q₀ hQ₀1 (hQ₀c.trans (mul_le_of_le_one_left (by linarith) hcε1.le)) (hcεN Q₀ hQ₀c)
    rw [hA, ← two_mul, ← mul_assoc, hB] at hw
    have h2C : (Real.sqrt (2 * C₁)) ^ 2 = 2 * C₁ := Real.sq_sqrt (by positivity)
    have := hsq (Real.sqrt (2 * C₁)) ht1 (by rw [h2C]; linarith)
    exact this.trans (mul_le_mul_of_nonneg_left hXmain ht1)
  -- (iii) `Q₀ > cε N`
  have hsqrtN : Real.sqrt N ≤ L ^ κ * N ^ lam := by
    rw [Real.sqrt_eq_rpow]
    calc N ^ (1 / 2 : ℝ) ≤ N ^ lam := hN12
      _ = 1 * N ^ lam := (one_mul _).symm
      _ ≤ L ^ κ * N ^ lam := mul_le_mul_of_nonneg_right hLκ (by positivity)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hscε : 0 < Real.sqrt cε := Real.sqrt_pos.2 hcε0
  rcases lt_or_ge (cε * N) 1 with hcN | hcN
  · -- (iii-a) `cε N < 1`: `N < 1/cε`, trivial bound
    refine ⟨3 / Real.sqrt cε, by linarith, ?_⟩
    have hNc : N ≤ cε⁻¹ := by
      have : N * cε ≤ cε⁻¹ * cε := by
        rw [inv_mul_cancel₀ hcε0.ne', mul_comm]
        exact hcN.le
      exact le_of_mul_le_mul_right this hcε0
    have hsN : Real.sqrt N ≤ 1 / Real.sqrt cε := by
      rw [one_div, ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt hNc
    calc _ ≤ 3 * N := hS3N
      _ = 3 * (Real.sqrt N * Real.sqrt N) := by rw [Real.mul_self_sqrt hN.le]
      _ ≤ 3 * ((1 / Real.sqrt cε) * Real.sqrt N) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hsN hsN0
      _ = 3 / Real.sqrt cε * Real.sqrt N := by ring
      _ ≤ 3 / Real.sqrt cε * (L ^ κ * N ^ lam) := mul_le_mul_of_nonneg_left hsqrtN ht2
      _ ≤ 3 / Real.sqrt cε * X := mul_le_mul_of_nonneg_left hXmain ht2
  · -- (iii-b) `Q = cε N`
    refine ⟨Real.sqrt (2 * C₁ / cε), by linarith, ?_⟩
    have hw := hwb (cε * N) hcN (mul_le_of_le_one_left (by linarith) hcε1.le) (hcεN _ le_rfl)
    have hQk : (cε * N) ^ k ≤ Q₀ ^ k := Real.rpow_le_rpow (by positivity) hQ₀c.le hk0
    have hterm : (cε * N) ^ k * L ^ k * N ^ (l - k + 1) ≤ N ^ 2 / (cε * N) := by
      calc (cε * N) ^ k * L ^ k * N ^ (l - k + 1) ≤ Q₀ ^ k * L ^ k * N ^ (l - k + 1) := by
            gcongr
        _ = N ^ 2 / Q₀ := hA
        _ ≤ N ^ 2 / (cε * N) := div_le_div_of_nonneg_left (by positivity) (by positivity) hQ₀c.le
    have hNc : N ^ 2 / (cε * N) = N / cε := by first | (field_simp; done) | (field_simp; ring)
    have h2C : (Real.sqrt (2 * C₁ / cε)) ^ 2 = 2 * C₁ / cε := Real.sq_sqrt (by positivity)
    have hle : ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤ (Real.sqrt (2 * C₁ / cε) * Real.sqrt N) ^ 2 := by
      rw [mul_pow, h2C, Real.sq_sqrt hN.le]
      calc _ ≤ C₁ * (N ^ 2 / (cε * N) + (cε * N) ^ k * L ^ k * N ^ (l - k + 1)) := hw
        _ ≤ C₁ * (N ^ 2 / (cε * N) + N ^ 2 / (cε * N)) := by
            apply mul_le_mul_of_nonneg_left _ hC₁0
            linarith
        _ = 2 * C₁ / cε * N := by rw [hNc]; field_simp; ring
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
    calc _ ≤ Real.sqrt (2 * C₁ / cε) * Real.sqrt N := this
      _ ≤ Real.sqrt (2 * C₁ / cε) * (L ^ κ * N ^ lam) := mul_le_mul_of_nonneg_left hsqrtN ht3
      _ ≤ Real.sqrt (2 * C₁ / cε) * X := mul_le_mul_of_nonneg_left hXmain ht3


/-- `A(1/2, 1/2) = (1/6, 2/3)` is an exponent pair. -/
theorem isExponentPair_sixth_two_thirds : IsExponentPair (1 / 6) (2 / 3) := by
  have := isExponentPair_A isExponentPair_half_half
  norm_num at this
  exact this


end AP

end LeanProofs.IntegerPoints
