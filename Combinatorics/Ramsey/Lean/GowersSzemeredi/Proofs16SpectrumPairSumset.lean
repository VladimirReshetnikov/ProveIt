import GowersSzemeredi.Proofs16BohrSpectrumBudget
import GowersSzemeredi.Proofs05PhaseMetric

/-! Sums of two difference sets contain a Bohr set on the common large
spectrum: the Fourier core of [49]'s Theorem 27, in `ℤ/N`.

Write `Â = fourier (indicator A)`. The weight `w(ξ) = |Â(ξ)|²|Â′(ξ)|²` is
the transform of the four-fold convolution, so
`Σ_ξ w(ξ) e(ξx) = N·#{(a,b,a′,b′) : a − b + a′ − b′ = x}`. If `S` contains
every frequency at which both transforms are at least `εN`, then for
`x ∈ B(S; 1/4)` every character in `S` has nonnegative real part at `x`. The
frequencies outside `S` contribute at most `(εN)²·N(|A|+|A′|)` by
Parseval. Hence `x ∈ (A − A) + (A′ − A′)` once
`ε²N³(|A|+|A′|) < |A|²|A′|²`.

* `norm_sq_fourier_indicator`: `|Â(ξ)|² = Σ_{a,b∈A} e((b−a)ξ)`.
* `sum_norm_sq_fourier_indicator`: Parseval, `Σ_ξ |Â(ξ)|² = N|A|`.
* `re_exponential_nonneg`: `Re e(y) ≥ 0` when `|y| ≤ N/4`.
* `sumset_contains_bohr_of_spectrum_pair`: the containment, for arbitrary
  sets and an arbitrary covering set `S`.
* `bohr_sumset_contains_span_intersection`: with the explicit bounded-span
  cutoff of `Proofs16BohrSpectrumBudget`, the sum of differences of two
  Bohr sets contains the Bohr set of the intersection of the two bounded
  spans at radius `1/4`. This is [49] Theorem 27 in `ℤ/N` with polynomial
  bounds; the condition `ε²N³(|B|+|B′|) < |B|²|B′|²` is kept explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **The squared transform of an indicator.** -/
theorem norm_sq_fourier_indicator {N : Nat} [NeZero N] (A : Finset (ZMod N)) (ξ : ZMod N) :
    (‖fourier (indicator A) ξ‖ : Complex) ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A, exponential ((b - a) * ξ) := by
  rw [← Complex.mul_conj', fourier_indicator_eq_sum, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← AddChar.map_neg_eq_conj, neg_neg, ← AddChar.map_add_eq_mul]
  unfold exponential
  congr 1
  ring

/-- Orthogonality of the characters. -/
theorem sum_exponential_mul_eq_ite {N : Nat} [NeZero N] (y : ZMod N) :
    ∑ ξ : ZMod N, exponential (y * ξ) = if y = 0 then (N : Complex) else 0 := by
  have h := AddChar.sum_mulShift y (ZMod.isPrimitive_stdAddChar N)
  simp only [ZMod.card] at h
  have hc : ∑ ξ : ZMod N, exponential (y * ξ) = ∑ ξ : ZMod N, ZMod.stdAddChar (ξ * y) :=
    Finset.sum_congr rfl fun ξ _ => by unfold exponential; rw [mul_comm]
  rw [hc, h]
  split_ifs <;> simp

/-- **Parseval for indicators.** -/
theorem sum_norm_sq_fourier_indicator {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    ∑ ξ : ZMod N, ‖fourier (indicator A) ξ‖ ^ 2 = N * A.card := by
  have h : ((∑ ξ : ZMod N, ‖fourier (indicator A) ξ‖ ^ 2 : Real) : Complex) =
      ((N * A.card : Real) : Complex) := by
    push_cast
    simp_rw [norm_sq_fourier_indicator]
    calc ∑ ξ : ZMod N, ∑ a ∈ A, ∑ b ∈ A, exponential ((b - a) * ξ)
        = ∑ a ∈ A, ∑ b ∈ A, ∑ ξ : ZMod N, exponential ((b - a) * ξ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a ∈ A, ∑ b ∈ A, if b = a then (N : Complex) else 0 := by
          simp_rw [sum_exponential_mul_eq_ite, sub_eq_zero]
      _ = ∑ _a ∈ A, (N : Complex) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_ite_eq', if_pos ha]
      _ = N * A.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  exact_mod_cast h

/-- **A character is in the right half-plane on the quarter ball.** -/
theorem re_exponential_nonneg {N : Nat} [NeZero N] {y : ZMod N}
    (hy : (centeredAbs y : Real) ≤ 1 / 4 * N) : 0 ≤ (exponential y).re := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [exponential_eq_exp_valMinAbs, mul_comm, Complex.exp_ofReal_mul_I_re]
  have hv : |((y.valMinAbs : Int) : Real)| ≤ N / 4 := by
    have : |((y.valMinAbs : Int) : Real)| = (centeredAbs y : Real) := by
      unfold centeredAbs
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    linarith
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · rw [le_div_iff₀ hNR]
    have := neg_abs_le ((y.valMinAbs : Int) : Real)
    nlinarith [Real.pi_pos]
  · rw [div_le_iff₀ hNR]
    have := le_abs_self ((y.valMinAbs : Int) : Real)
    nlinarith [Real.pi_pos]

/-- The four-fold sum, written with the transforms. -/
theorem sum_weight_exponential {N : Nat} [NeZero N] (A A' : Finset (ZMod N)) (x : ZMod N) :
    ∑ ξ : ZMod N, ((‖fourier (indicator A) ξ‖ ^ 2 * ‖fourier (indicator A') ξ‖ ^ 2 : Real) :
        Complex) * exponential (ξ * x) =
      ∑ a ∈ A, ∑ b ∈ A, ∑ a' ∈ A', ∑ b' ∈ A',
        if (b - a) + (b' - a') + x = 0 then (N : Complex) else 0 := by
  have hexp : ∀ ξ : ZMod N, ((‖fourier (indicator A) ξ‖ ^ 2 * ‖fourier (indicator A') ξ‖ ^ 2 :
      Real) : Complex) * exponential (ξ * x) =
      ∑ a ∈ A, ∑ b ∈ A, ∑ a' ∈ A', ∑ b' ∈ A',
        exponential (((b - a) + (b' - a') + x) * ξ) := by
    intro ξ
    push_cast
    rw [norm_sq_fourier_indicator, norm_sq_fourier_indicator, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a' _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b' _
    unfold exponential
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a' _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b' _
  exact sum_exponential_mul_eq_ite _

/-- **Two difference sets sum to a Bohr set on the common large spectrum.** -/
theorem sumset_contains_bohr_of_spectrum_pair {N : Nat} [NeZero N]
    (A A' S : Finset (ZMod N)) {epsilon : Real}
    (hS : ∀ ξ, epsilon * N ≤ ‖fourier (indicator A) ξ‖ →
      epsilon * N ≤ ‖fourier (indicator A') ξ‖ → ξ ∈ S)
    (hbudget : epsilon ^ 2 * (N : Real) ^ 3 * (A.card + A'.card) <
      (A.card : Real) ^ 2 * (A'.card : Real) ^ 2)
    {x : ZMod N} (hx : x ∈ bohr S (1 / 4)) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ a' ∈ A', ∃ b' ∈ A', x = a - b + (a' - b') := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  by_contra hno
  push Not at hno
  -- the four-fold count at `x` vanishes
  have hzero : ∑ ξ : ZMod N, ((‖fourier (indicator A) ξ‖ ^ 2 *
      ‖fourier (indicator A') ξ‖ ^ 2 : Real) : Complex) * exponential (ξ * x) = 0 := by
    rw [sum_weight_exponential]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb =>
      Finset.sum_eq_zero fun a' ha' => Finset.sum_eq_zero fun b' hb' => if_neg ?_
    intro h
    exact hno a ha b hb a' ha' b' hb' (by linear_combination h)
  obtain ⟨w, hw⟩ : ∃ w : ZMod N → Real, w = fun ξ =>
      ‖fourier (indicator A) ξ‖ ^ 2 * ‖fourier (indicator A') ξ‖ ^ 2 := ⟨_, rfl⟩
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => by rw [hw]; positivity
  have hre : ∑ ξ : ZMod N, w ξ * (exponential (ξ * x)).re = 0 := by
    have := congrArg Complex.re hzero
    rw [Complex.re_sum] at this
    simp only [Complex.re_ofReal_mul, Complex.zero_re] at this
    rw [hw]
    exact this
  set S' := insert 0 S
  -- on `S'` every term is nonnegative
  have hin : ∀ ξ ∈ S', 0 ≤ w ξ * (exponential (ξ * x)).re := by
    intro ξ hξ
    apply mul_nonneg (hw0 ξ)
    apply re_exponential_nonneg
    rcases Finset.mem_insert.mp hξ with rfl | hξ
    · simp [centeredAbs]
    · exact (Finset.mem_filter.mp hx).2 ξ hξ
  -- off `S'` the weight is small
  have hout : ∀ ξ ∉ S', w ξ ≤ (epsilon * N) ^ 2 *
      (‖fourier (indicator A) ξ‖ ^ 2 + ‖fourier (indicator A') ξ‖ ^ 2) := by
    intro ξ hξ
    have hξS : ξ ∉ S := fun h => hξ (Finset.mem_insert_of_mem h)
    by_cases h1 : epsilon * N ≤ ‖fourier (indicator A) ξ‖
    · have h2 : ‖fourier (indicator A') ξ‖ < epsilon * N := by
        by_contra h2; push Not at h2; exact hξS (hS ξ h1 h2)
      have h2' : ‖fourier (indicator A') ξ‖ ^ 2 ≤ (epsilon * N) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2.le 2
      have := mul_le_mul_of_nonneg_left h2' (sq_nonneg ‖fourier (indicator A) ξ‖)
      simp only [hw]
      nlinarith [sq_nonneg ‖fourier (indicator A') ξ‖, sq_nonneg (epsilon * N)]
    · push Not at h1
      have h1' : ‖fourier (indicator A) ξ‖ ^ 2 ≤ (epsilon * N) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1.le 2
      have := mul_le_mul_of_nonneg_right h1' (sq_nonneg ‖fourier (indicator A') ξ‖)
      simp only [hw]
      nlinarith [sq_nonneg ‖fourier (indicator A) ξ‖, sq_nonneg (epsilon * N)]
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S')
    fun ξ => w ξ * (exponential (ξ * x)).re).symm
  rw [hre] at hsplit
  -- the inner part is at least the zero frequency
  have hfilt : (Finset.univ.filter fun ξ : ZMod N => ξ ∈ S') = S' := by
    ext ξ; simp
  have hinner : w 0 ≤ ∑ ξ ∈ Finset.univ.filter (· ∈ S'), w ξ * (exponential (ξ * x)).re := by
    rw [hfilt]
    have h0 : w 0 = w 0 * (exponential (0 * x)).re := by simp [exponential]
    rw [h0]
    exact Finset.single_le_sum hin (Finset.mem_insert_self 0 S)
  have houter : -((epsilon * N) ^ 2 * (N * A.card + N * A'.card)) ≤
      ∑ ξ ∈ Finset.univ.filter (· ∉ S'), w ξ * (exponential (ξ * x)).re := by
    have hle : ∀ ξ ∈ Finset.univ.filter (· ∉ S'), -((epsilon * N) ^ 2 *
        (‖fourier (indicator A) ξ‖ ^ 2 + ‖fourier (indicator A') ξ‖ ^ 2)) ≤
        w ξ * (exponential (ξ * x)).re := by
      intro ξ hξ
      have hξ' := (Finset.mem_filter.mp hξ).2
      have hb := hout ξ hξ'
      have hre1 : -1 ≤ (exponential (ξ * x)).re := by
        have h1 : ‖exponential (ξ * x)‖ = 1 := (ZMod.stdAddChar (N := N)).norm_apply _
        have := Complex.abs_re_le_norm (exponential (ξ * x))
        rw [h1] at this
        linarith [neg_abs_le (exponential (ξ * x)).re]
      nlinarith [hw0 ξ]
    have hsum := Finset.sum_le_sum hle
    have hall : ∑ ξ ∈ Finset.univ.filter (· ∉ S'),
        (‖fourier (indicator A) ξ‖ ^ 2 + ‖fourier (indicator A') ξ‖ ^ 2) ≤
        N * A.card + N * A'.card := by
      calc _ ≤ ∑ ξ : ZMod N, (‖fourier (indicator A) ξ‖ ^ 2 + ‖fourier (indicator A') ξ‖ ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ξ _ _ => by positivity)
        _ = _ := by
            rw [Finset.sum_add_distrib, sum_norm_sq_fourier_indicator,
              sum_norm_sq_fourier_indicator]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
    have hmul := mul_le_mul_of_nonneg_left hall (sq_nonneg (epsilon * N))
    linarith
  have hw0val : w 0 = (A.card : Real) ^ 2 * (A'.card : Real) ^ 2 := by
    simp only [hw]
    have hA : ∀ B : Finset (ZMod N), ‖fourier (indicator B) 0‖ = B.card := by
      intro B
      rw [fourier_indicator_eq_sum]
      simp
    rw [hA, hA]
  have : (epsilon * N) ^ 2 * (N * A.card + N * A'.card) =
      epsilon ^ 2 * (N : Real) ^ 3 * (A.card + A'.card) := by ring
  linarith

/-- **[49] Theorem 27 in `ℤ/N`.** The differences of two Bohr sets sum to the
Bohr set of the intersection of their bounded spans at radius `1/4`. -/
theorem bohr_sumset_contains_span_intersection {N : Nat} [NeZero N] [Fact N.Prime]
    (K K' : Finset (ZMod N)) {a c a' c' : Nat} (hca : c ≤ a) (hca' : c' ≤ a')
    (ha : 2 * a < N) (hc : 2 * c < N) (ha' : 2 * a' < N) (hc' : 2 * c' < N)
    {epsilon : Real} (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hband : K.card * (4 * (c : Real) + 2) ≤ epsilon / 2 * N)
    (hband' : K'.card * (4 * (c' : Real) + 2) ≤ epsilon / 2 * N)
    (hbudget : epsilon ^ 2 * (N : Real) ^ 3 *
        ((bohr K ((a : Real) / N)).card + (bohr K' ((a' : Real) / N)).card) <
      ((bohr K ((a : Real) / N)).card : Real) ^ 2 *
        ((bohr K' ((a' : Real) / N)).card : Real) ^ 2)
    {x : ZMod N}
    (hx : x ∈ bohr
      (boundedFrequencySpan (fun gamma : K => (gamma : ZMod N))
          ⌈8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card)⌉₊ ∩
        boundedFrequencySpan (fun gamma : K' => (gamma : ZMod N))
          ⌈8 * (K'.card + 1 : Real) * N / (epsilon * (centeredBall N c').card)⌉₊) (1 / 4)) :
    ∃ y ∈ bohr K ((a : Real) / N), ∃ z ∈ bohr K ((a : Real) / N),
      ∃ y' ∈ bohr K' ((a' : Real) / N), ∃ z' ∈ bohr K' ((a' : Real) / N),
        x = y - z + (y' - z') :=
  sumset_contains_bohr_of_spectrum_pair _ _ _
    (fun _ h h' => Finset.mem_inter.mpr
      ⟨large_bohr_fourier_mem_explicit_boundedSpan K hca ha hc heps heps1 hband h,
        large_bohr_fourier_mem_explicit_boundedSpan K' hca' ha' hc' heps heps1 hband' h'⟩)
    hbudget hx

end LeanProofs.GowersSzemeredi
