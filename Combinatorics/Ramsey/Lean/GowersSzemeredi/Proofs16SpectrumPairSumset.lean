import GowersSzemeredi.Proofs16BohrSumSpan
import GowersSzemeredi.Proofs05PhaseMetric

/-! A quarter-radius mixed Bogolyubov theorem: a sharper form of
`mixed_bogolyubov` and of the Bohr-sum containment of [49]'s Theorem 27.

`mixed_bogolyubov` (`Proofs16MixedBogolyubov`) controls `(A − A) + (B − B)`
by the Bohr set of the common large spectrum at radius `1/(4π)`, with
coefficient threshold `τ = |A||B|/(4N²)`. Bounding the phase error by `1/2`
costs the factor `π` in the radius. Using instead that every character has
nonnegative real part on the quarter ball gives

* radius `1/4`, the radius in [49]'s Theorem 27 (`π` times larger); and
* threshold `2τ = |A||B|/(2N²)` (twice larger), so fewer frequencies are
  large and the bounded-span cutoff `128(m+1)²/ε²` shrinks by a factor of
  four.

Write `w(ξ) = |Â(ξ)|²|B̂(ξ)|²` (`mixedFourierWeight`). Then
`Σ_ξ w(ξ) e(ξx)` is `N` times the number of representations of `x` in
`(A − A) + (B − B)` (`sum_weight_exponential`). On `B(S; 1/4)` the terms
with `ξ ∈ S` have nonnegative real part (`re_exponential_nonneg`). The
terms off `S` have total weight at most `(εN)²·N(|A|+|B|)` by Parseval
(`indicator_fourier_energy`). The zero term `|A|²|B|²` wins once
`ε²N³(|A|+|B|) < |A|²|B|²`.

* `norm_sq_fourier_indicator`: `|Â(ξ)|² = Σ_{a,b∈A} e((b−a)ξ)`.
* `sum_exponential_mul_eq_ite`: character orthogonality.
* `sumset_contains_bohr_of_spectrum_pair`: the containment for an
  arbitrary covering set `S` and threshold `ε`.
* `mixed_bogolyubov_quarter`: the common large spectrum at threshold
  `|A||B|/(2N²)`, radius `1/4`.
* `bohr_sum_of_common_spectrum_quarter` and
  `bohr_sum_contains_span_intersection_quarter`: the Bohr-sum
  containments of `Proofs16BohrSumSpan` at radius `1/4` and threshold
  `2·bohrSumThreshold`. -/
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
            rw [Finset.sum_add_distrib, indicator_fourier_energy,
              indicator_fourier_energy]
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

/-- The quarter-radius budget holds at threshold `|A||B|/(2N²)`. -/
theorem quarter_threshold_budget {N : Nat} [NeZero N] (A B : Finset (ZMod N))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ((A.card : Real) * B.card / (2 * (N : Real) ^ 2)) ^ 2 * (N : Real) ^ 3 *
        (A.card + B.card) < (A.card : Real) ^ 2 * (B.card : Real) ^ 2 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hAc : (0 : Real) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBc : (0 : Real) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hAN : (A.card : Real) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa using Finset.card_le_univ A)
  have hBN : (B.card : Real) ≤ N := by
    exact_mod_cast (show B.card ≤ N by simpa using Finset.card_le_univ B)
  have heq : ((A.card : Real) * B.card / (2 * (N : Real) ^ 2)) ^ 2 * (N : Real) ^ 3 *
      (A.card + B.card) =
      (A.card : Real) ^ 2 * (B.card : Real) ^ 2 * ((A.card + B.card) / (4 * N)) := by
    field_simp
    ring
  rw [heq]
  have hfrac : ((A.card : Real) + B.card) / (4 * N) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hpos : (0 : Real) < (A.card : Real) ^ 2 * (B.card : Real) ^ 2 := by positivity
  nlinarith

/-- **Mixed Bogolyubov at radius `1/4`.** -/
theorem mixed_bogolyubov_quarter {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (hA : A.Nonempty) (hB : B.Nonempty) (d : ZMod N)
    (hd : d ∈ bohr (commonLargeSpectrum A B ((A.card : Real) * B.card / (2 * (N : Real) ^ 2)))
      (1 / 4)) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = (a₁ - a₂) + (b₁ - b₂) :=
  sumset_contains_bohr_of_spectrum_pair A B _
    (fun _ h h' => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, h'⟩)
    (quarter_threshold_budget A B hA hB) hd

/-- The common large spectrum of the half-radius sets, at twice the
threshold and radius `1/4`, controls their sum. -/
theorem bohr_sum_of_common_spectrum_quarter {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) {rho sigma : Real} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (d : ZMod N)
    (hd : d ∈ bohr (commonLargeSpectrum (bohr K (rho / 2)) (bohr L (sigma / 2))
      (2 * bohrSumThreshold K L rho sigma)) (1 / 4)) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  have hthr : 2 * bohrSumThreshold K L rho sigma =
      ((bohr K (rho / 2)).card : Real) * (bohr L (sigma / 2)).card / (2 * (N : Real) ^ 2) := by
    unfold bohrSumThreshold
    ring
  rw [hthr] at hd
  obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hd'⟩ :=
    mixed_bogolyubov_quarter (bohr K (rho / 2)) (bohr L (sigma / 2))
      ⟨0, zero_mem_bohr K (show 0 ≤ rho / 2 by positivity)⟩
      ⟨0, zero_mem_bohr L (show 0 ≤ sigma / 2 by positivity)⟩ d hd
  refine ⟨a₁ - a₂, ?_, b₁ - b₂, ?_, hd'⟩
  · simpa only [sub_eq_add_neg] using bohr_add_half ha₁ (neg_mem_bohr ha₂)
  · simpa only [sub_eq_add_neg] using bohr_add_half hb₁ (neg_mem_bohr hb₂)

/-- **[49] Theorem 27 in `ℤ/N`, at radius `1/4`.** The Bohr set of the
intersection of the two bounded frequency spans, at radius `1/4`, lies in
`B(K;ρ) + B(L;σ)`. Compared with `bohr_sum_contains_span_intersection` the
radius is `π` times larger and the threshold twice larger. -/
theorem bohr_sum_contains_span_intersection_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hNK : 8 * (K.card + 1 : Real) / (2 * bohrSumThreshold K L rho sigma) ≤ (N : Real))
    (hNL : 8 * (L.card + 1 : Real) / (2 * bohrSumThreshold K L rho sigma) ≤ (N : Real))
    (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (2 * bohrSumThreshold K L rho sigma)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (2 * bohrSumThreshold K L rho sigma)))
      (1 / 4)) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard (T : Finset (ZMod N)) {r : Real} (hr : 0 ≤ r) :
      0 < ((bohr T r).card : Real) ∧ ((bohr T r).card : Real) ≤ N := by
    constructor
    · exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_bohr T hr⟩
    · exact_mod_cast (show (bohr T r).card ≤ N by simpa using Finset.card_le_univ (bohr T r))
  obtain ⟨hA, hAN⟩ := hcard K (show 0 ≤ rho / 2 by positivity)
  obtain ⟨hB, hBN⟩ := hcard L (show 0 ≤ sigma / 2 by positivity)
  have htau : 0 < 2 * bohrSumThreshold K L rho sigma := by
    unfold bohrSumThreshold; positivity
  have htau1 : 2 * bohrSumThreshold K L rho sigma ≤ 1 := by
    unfold bohrSumThreshold
    rw [show 2 * (((bohr K (rho / 2)).card : Real) * (bohr L (sigma / 2)).card /
        (4 * (N : Real) ^ 2)) = ((bohr K (rho / 2)).card : Real) * (bohr L (sigma / 2)).card /
        (2 * (N : Real) ^ 2) by ring]
    rw [div_le_one (by positivity)]
    have hmul := mul_le_mul hAN hBN hB.le hNR.le
    nlinarith [sq_nonneg (N : Real)]
  apply bohr_sum_of_common_spectrum_quarter K L hrho.le hsigma.le d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hlarge := (Finset.mem_filter.mp hr).2
  have hK := large_bohr_fourier_mem_polynomial_boundedSpan K (half_pos hrho)
    (by linarith : rho / 2 < 1 / 2) htau htau1 hNK hlarge.1
  have hL := large_bohr_fourier_mem_polynomial_boundedSpan L (half_pos hsigma)
    (by linarith : sigma / 2 < 1 / 2) htau htau1 hNL hlarge.2
  exact (Finset.mem_filter.mp hd).2 r (Finset.mem_inter.mpr ⟨hK, hL⟩)

end LeanProofs.GowersSzemeredi
