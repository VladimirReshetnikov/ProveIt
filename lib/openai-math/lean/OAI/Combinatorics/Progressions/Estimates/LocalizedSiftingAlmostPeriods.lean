import OAI.Combinatorics.Progressions.Estimates.LocalizedCorrelationMoment
import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression
import OAI.Combinatorics.Progressions.Fourier.RationalBohrWidth
import OAI.Combinatorics.Progressions.Geometry.DifferenceEventSupport
import OAI.Combinatorics.Progressions.Probability.SiftingDensityBudget
import OAI.Combinatorics.Progressions.Sampling.QuarticSamplingBudget

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def goodDifferenceSet (S T : Finset G) (f : G → ℝ) (threshold : ℝ) : Finset G :=
  (S - T).filter (fun x => threshold ≤ f x)

theorem goodDifferenceSet_subset (S T : Finset G) (f : G → ℝ) (threshold : ℝ) :
    goodDifferenceSet S T f threshold ⊆ S - T := Finset.filter_subset _ _

theorem le_of_mem_goodDifferenceSet {S T : Finset G} {f : G → ℝ} {threshold : ℝ} {x : G}
    (hx : x ∈ goodDifferenceSet S T f threshold) : threshold ≤ f x :=
  (Finset.mem_filter.mp hx).2

theorem le_threshold_of_not_mem_goodDifferenceSet
    {S T : Finset G} {f : G → ℝ} {threshold : ℝ} {a b : G}
    (ha : a ∈ S) (hb : b ∈ T) (hnot : a - b ∉ goodDifferenceSet S T f threshold) :
    f (a - b) ≤ threshold := by
  have hmem : a - b ∈ S - T := Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩
  have h : ¬ threshold ≤ f (a - b) := by
    intro hle
    exact hnot (Finset.mem_filter.mpr ⟨hmem, hle⟩)
  exact (lt_of_not_ge h).le

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

theorem sqrt_le_exp_of_le_exp_two_mul {beta p : ℝ} (hbeta : beta ≤ Real.exp (2 * p)) :
    Real.sqrt beta ≤ Real.exp p := by
  apply (Real.sqrt_le_left (Real.exp_pos p).le).mpr
  simpa only [two_mul, Real.exp_add, pow_two] using hbeta

theorem old_frequency_scale_le_regularity {epsilon p d : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) (hd : 0 < d) :
    epsilon * Real.exp (-p) / (6400 * d) ≤ 1 / (200 * d) := by
  have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : epsilon * Real.exp (-p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left he hepsilon).trans (by simpa using hepsilon1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem chosen_scales_error_le
    {epsilon p d D dim beta : ℝ} (hepsilon : 0 < epsilon) (hd : 0 < d)
    (hD : 0 ≤ D) (hdim0 : 0 ≤ dim) (hdim : dim ≤ D)
    (hbeta : beta ≤ Real.exp (2 * p)) :
    2 * (epsilon / 8) +
      (dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
        800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
        2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p) * Real.sqrt beta ≤ epsilon := by
  have hcancel : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add]
    simp
  have hDpos : 0 < D + 1 := by linarith
  have hnew : dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p ≤ epsilon / 8 := by
    calc
      _ ≤ (D + 1) * (epsilon * Real.exp (-p) / (8 * (D + 1))) * Real.exp p := by
        gcongr
        linarith
      _ = epsilon / 8 := by
        field_simp
        nlinarith [hcancel]
  have hold : 800 * d * (epsilon * Real.exp (-p) / (6400 * d)) * Real.exp p = epsilon / 8 := by
    field_simp
    nlinarith [hcancel]
  have htail : 2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 8 := by
    have h := half_pow_spectralIterations_mul_exp_le (p := p) hepsilon
    linarith
  have hsqrt := sqrt_le_exp_of_le_exp_two_mul hbeta
  have hfactor : 0 ≤ dim * (epsilon * Real.exp (-p) / (8 * (D + 1))) +
      800 * d * (epsilon * Real.exp (-p) / (6400 * d)) +
      2 * (1 / 2 : ℝ) ^ spectralIterations epsilon p := by positivity
  have hbound := mul_le_mul_of_nonneg_left hsqrt hfactor
  nlinarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_quartic_local_almostPeriods
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A L : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p))
    (hdoubling : ((A + B.carrier).card : ℝ) ≤ (2 * Real.exp p) * A.card) :
    let D := rankQuarticFactor epsilon * (p + 1) ^ 4
    let d := max B.rank 1
    let a : ℝ≥0 := (100 * ((2 * d : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
    let sigma := epsilon * Real.exp (-p) / (6400 * (d : ℝ))
    let r := epsilon * Real.exp (-p) / (8 * (D + 1))
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + D ∧
      min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤ R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧ ∀ t ∈ R.carrier, ∀ x, |u (x + t) - u x| ≤ epsilon := by
  intro D d a sigma r u
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (rankQuarticFactor_pos epsilon).le (pow_nonneg (by positivity) _)
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  let sigmaN : ℝ≥0 := ⟨sigma, hsigma.le⟩
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hsigreg : sigmaN ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by
    have h := old_frequency_scale_le_regularity hepsilon.le hepsilon1 hp hd
    change sigma ≤ ((1 : ℝ) / (100 * ((2 * max B.rank 1 : ℕ) : ℝ)))
    dsimp [sigma, d] at h ⊢
    push_cast at h ⊢
    convert h using 1
    ring
  let q := spectralIterations epsilon p
  let k := crootSisaskSampleSize (convolutionMomentOrder M L) (((epsilon / 8) / q) / Real.exp 1)
  obtain ⟨T, R, hT, hTB, hcount, hRreg, hRrank, hRwidth, hRupper, hRB, hshift⟩ :=
    exists_local_bohr_triple_almostPeriods_relative B hBpos hBreg hA B.carrier_nonempty hL
      (fun _ h => h) M q (spectralIterations_pos epsilon p)
      (by positivity : 0 < epsilon / 8) sigmaN rN hsigma hr hsigreg
  have hcount' : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card :=
    samplingDensity_le_of_smallDoubling hA B.carrier_nonempty k (by positivity) hdoubling hcount
  have hk : (k : ℝ) ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 :=
    local_sample_size_le_cubic M L hepsilon hepsilon1 hp hratio
  have hdim : localChangDimension B T (1 / 2) ≤ D :=
    local_dimension_le_quartic_of_cubic_sampling B hT hp (samplingCubicFactor_pos epsilon).le k hk hcount'
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) := by
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hcard : (T.card : ℝ) ≤ B.carrier.card := by exact_mod_cast Finset.card_le_card hTB
    have hratio1 : 1 ≤ 2 * (B.carrier.card : ℝ) / T.card := by
      rw [le_div_iff₀ hTpos]
      linarith
    have hlog := Real.log_nonneg hratio1
    unfold localChangDimension
    positivity
  have ha : a ≤ localChangBaseScale B T (1 / 2) :=
    localChangBaseScale_ge_of_dimension_le B T (1 / 2) D hdim
  refine ⟨R, hRreg, hRrank.trans (add_le_add le_rfl hdim), ?_, hRupper, hRB, ?_⟩
  · apply le_trans _ hRwidth
    change min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤
      min (sigma * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2
    gcongr
  · intro t ht x
    apply (hshift t ht x).trans
    exact chosen_scales_error_le hepsilon hd hD hdim0 hdim hratio

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem smoothed_correlation_ge_of_good_probability
    (L A B K R : Finset (ZMod N)) (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) {threshold : ℝ}
    (hK : ∀ x ∈ K, threshold ≤ correlation L f f x) :
    threshold * smoothedDifferenceEventProbability A B K R ≤
      𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R, correlation L f f (a - b + t) := by
  rw [smoothedDifferenceEventProbability_eq_average]
  simp only [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro a _
  apply Finset.expect_le_expect
  intro b _
  apply Finset.expect_le_expect
  intro t _
  by_cases h : a - b + t ∈ K
  · simpa only [realSetIndicator, h, ite_true, mul_one] using hK _ h
  · simpa only [realSetIndicator, h, ite_false, mul_zero] using correlation_nonneg L f f hf hf _

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

noncomputable def almostPeriodicityWidthConstant (epsilon : ℝ) : ℝ :=
  10240000000 * (rankQuarticFactor epsilon + 1) / epsilon + 8

theorem almostPeriodicityWidthConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  unfold almostPeriodicityWidthConstant
  positivity

theorem rankQuarticFactor_le_widthConstant {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    rankQuarticFactor epsilon ≤ almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  have hprod := mul_le_mul_of_nonneg_left hepsilon1 hC.le
  have hquot : rankQuarticFactor epsilon ≤
      10240000000 * (rankQuarticFactor epsilon + 1) / epsilon := by
    rw [le_div_iff₀ hepsilon]
    nlinarith
  unfold almostPeriodicityWidthConstant
  linarith

variable {N : ℕ} [NeZero N]

theorem exists_difference_event_almostPeriods_with_width
    (S B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBwidth : B.radius ≤ 1)
    (hBreg : B.IsRankRegular) (hBrank : 1 ≤ B.rank)
    (A₁ A₂ K : Finset (ZMod N)) (z : ZMod N)
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 1 ≤ p)
    (hA₂B : ∀ a ∈ A₂, a - z ∈ B.carrier)
    (hdensity₁ : Real.exp (-p) * S.carrier.card ≤ A₁.card)
    (hdensity₂ : Real.exp (-p) * B.carrier.card ≤ A₂.card)
    (hK : K.card ≤ 2 * S.carrier.card) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      R.carrier ⊆ B.carrier ∧
      (R.rank : ℝ) ≤ B.rank + almostPeriodicityWidthConstant epsilon * (1 + p) ^ 4 ∧
      B.radius * Real.exp (-(almostPeriodicityWidthConstant epsilon *
        (1 + p + Real.log (2 + B.rank)))) ≤ R.radius ∧
      |smoothedDifferenceEventProbability A₁ A₂ K R.carrier - differenceEventProbability A₁ A₂ K 0| ≤
        epsilon := by
  have hp0 : 0 ≤ p := by linarith
  have hA₁pos : (0 : ℝ) < A₁.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast S.card_pos)).trans_le hdensity₁
  have hA₂pos : (0 : ℝ) < A₂.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast B.card_pos)).trans_le hdensity₂
  have hA₁ : A₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA₁pos)
  have hA₂ : A₂.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA₂pos)
  have hSsize : (S.carrier.card : ℝ) ≤ Real.exp p * A₁.card := by
    calc
      (S.carrier.card : ℝ) = Real.exp p * (Real.exp (-p) * S.carrier.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A₁.card :=
        mul_le_mul_of_nonneg_left hdensity₁ (Real.exp_pos p).le
  have htwo : 2 ≤ Real.exp p := Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hp)
  have hratio : (K.card : ℝ) / (-A₁).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hA₁pos]
    calc
      (K.card : ℝ) ≤ 2 * S.carrier.card := by exact_mod_cast hK
      _ ≤ 2 * (Real.exp p * A₁.card) := mul_le_mul_of_nonneg_left hSsize (by norm_num)
      _ ≤ Real.exp p * (Real.exp p * A₁.card) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (2 * p) * A₁.card := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
  obtain ⟨B₀, hfreq, hB₀reg, hB₀lo, hB₀hi, hB₀B, hsumset⟩ :=
    B.exists_initial_regular_sampling_bohr hBpos hBreg
  have hB₀rank : B₀.rank = B.rank := congrArg Finset.card hfreq
  have hd : (0 : ℝ) < B.rank := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hBrank)
  have hd1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
  have hscale : (B.initialSamplingScale : ℝ) = 1 / (200 * (B.rank : ℝ)) := by
    norm_num [CyclicBohr.Set.initialSamplingScale, max_eq_left hBrank]
    ring
  have hB₀lower : B.radius / (400 * (B.rank : ℝ)) ≤ B₀.radius := by
    rw [hscale] at hB₀lo
    convert hB₀lo using 1
    ring
  have hB₀pos : 0 < B₀.radius := lt_of_lt_of_le (by positivity) hB₀lower
  have hdoubling : ((A₂ + B₀.carrier).card : ℝ) ≤ (2 * Real.exp p) * A₂.card :=
    B.sumset_le_exp_of_relative_density (hsumset A₂ z hA₂B) hdensity₂
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, hRB₀, hshift⟩ :=
    exists_quartic_local_almostPeriods B₀ hB₀pos hB₀reg hA₂ hA₁.neg K
      hepsilon hepsilon1 hp0 hratio hdoubling
  let C := rankQuarticFactor epsilon
  let D := C * (p + 1) ^ 4
  have hC : 0 < C := rankQuarticFactor_pos epsilon
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdmax : max B₀.rank 1 = B.rank := by rw [hB₀rank, max_eq_left hBrank]
  let a : ℝ≥0 :=
    (100 * ((2 * max B₀.rank 1 : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have ha : 1 / (1000 * (B.rank : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa [a, hdmax] using BohrWidthBudget.selector_scale_lower_bound hd hD
  have hRrational : epsilon * Real.exp (-p) * B.radius /
      (10240000000 * (B.rank : ℝ) ^ 3 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := epsilon * Real.exp (-p)) (by positivity) hd1 hD hBpos hBwidth hB₀lower ha
    apply h.trans
    simpa only [a, D, C, hdmax] using hRwidth
  have hRexp : B.radius * Real.exp (-(almostPeriodicityWidthConstant epsilon *
      (1 + p + Real.log (2 + B.rank)))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential hepsilon hC.le hp0 hd1 B.radius_nonneg
    apply le_trans _ hRrational
    simpa only [almostPeriodicityWidthConstant, C, D] using h
  have hRpos : 0 < R.radius :=
    (mul_pos hBpos (Real.exp_pos _)).trans_le hRexp
  have hRone : R.radius ≤ 1 := by
    apply hRupper.trans
    have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hnum : epsilon * Real.exp (-p) ≤ 1 :=
      (mul_le_mul_of_nonneg_left he hepsilon.le).trans (by simpa using hepsilon1)
    apply (div_le_one (by positivity : 0 < 8 * (D + 1))).mpr
    nlinarith
  have hRrank' : (R.rank : ℝ) ≤ B.rank + almostPeriodicityWidthConstant epsilon * (1 + p) ^ 4 := by
    have hconst := rankQuarticFactor_le_widthConstant hepsilon hepsilon1
    rw [hB₀rank] at hRrank
    apply hRrank.trans
    rw [add_comm 1 p]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hconst (by positivity))
  refine ⟨R, hRreg, hRpos, hRone, hRB₀.trans hB₀B, hRrank', hRexp, ?_⟩
  exact differenceEventProbability_smoothing_of_triple_shifts A₁ A₂ K R.carrier_nonempty hshift

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

noncomputable def quarticBogolyubovConstant : ℝ :=
  3 * almostPeriodicityWidthConstant (1 / 2)

theorem quarticBogolyubovConstant_pos : 0 < quarticBogolyubovConstant := by
  exact mul_pos (by norm_num) (almostPeriodicityWidthConstant_pos (by norm_num))

theorem exists_quartic_bogolyubov {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius ∧
      R.carrier ⊆ 2 • A - 2 • A := by
  have hApos : (0 : ℝ) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hdensity
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hNle : (N : ℝ) ≤ Real.exp p * A.card := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hratio : ((A - A).card : ℝ) / (-A).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hApos]
    calc
      ((A - A).card : ℝ) ≤ N := by
        exact_mod_cast (show (A - A).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ (A - A))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ Real.exp (2 * p) * A.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hApos.le
  have hdoubling : ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤
      (2 * Real.exp p) * A.card := by
    calc
      ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ
            (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ (2 * Real.exp p) * A.card := by nlinarith [Real.exp_pos p]
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, _, hshift⟩ :=
    exists_quartic_local_almostPeriods CyclicBohr.Set.whole (by norm_num)
      CyclicBohr.Set.isRankRegular_whole hA hA.neg (A - A)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hp hratio hdoubling
  let C₀ := rankQuarticFactor (1 / 2)
  let D := C₀ * (p + 1) ^ 4
  let a : ℝ≥0 := (100 * 2 * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have hC₀ : 0 < C₀ := rankQuarticFactor_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  simp only [CyclicBohr.Set.rank_whole, CyclicBohr.Set.radius_whole, max_self,
    Nat.cast_one, Nat.cast_ofNat, mul_one] at hRrank hRwidth hRupper
  change (R.rank : ℝ) ≤ 1 + D at hRrank
  change min (((1 / 2 : ℝ) * Real.exp (-p) / 6400) * ((a : ℝ) / 2))
      (((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1))) / 2 ≤ R.radius at hRwidth
  change R.radius ≤ ((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1)) at hRupper
  have ha : 1 / (1000 * (1 : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa only [a, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_ofNat, mul_one] using BohrWidthBudget.selector_scale_lower_bound
        (d := 1) (by norm_num) hD
  have hRrat : ((1 / 2 : ℝ) * Real.exp (-p)) /
      (10240000000 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := (1 / 2 : ℝ) * Real.exp (-p)) (d := 1) (D := D) (w := 1) (v := 1)
      (by positivity) (by norm_num) hD (by norm_num) (by norm_num) (by norm_num) ha
    apply le_trans _ hRwidth
    simpa only [one_pow, mul_one] using h
  have hC : 0 < almostPeriodicityWidthConstant (1 / 2) :=
    almostPeriodicityWidthConstant_pos (by norm_num)
  have hRexp : Real.exp (-(almostPeriodicityWidthConstant (1 / 2) *
      (1 + p + Real.log 3))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential
      (epsilon := 1 / 2) (C := C₀) (p := p) (d := 1) (w := 1)
      (by norm_num) hC₀.le hp (by norm_num) (by norm_num)
    apply le_trans _ hRrat
    simpa only [almostPeriodicityWidthConstant, D, C₀, one_pow, mul_one, one_mul,
      show (2 : ℝ) + 1 = 3 by norm_num] using h
  have hlog : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hbudget : almostPeriodicityWidthConstant (1 / 2) * (1 + p + Real.log 3) ≤
      quarticBogolyubovConstant * (p + 1) := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    unfold quarticBogolyubovConstant
    nlinarith [mul_nonneg hC.le hp]
  have hwidth : Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius :=
    (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hRexp
  refine ⟨R, hRreg, (Real.exp_pos _).trans_le hwidth, ?_, ?_, hwidth, ?_⟩
  · apply hRupper.trans
    apply (div_le_one (by positivity)).mpr
    have h := Real.exp_le_one_iff.mpr (by linarith : -p ≤ 0)
    nlinarith
  · have hC₀C := rankQuarticFactor_le_widthConstant
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hCC : C₀ ≤ quarticBogolyubovConstant := by
      dsimp [C₀, quarticBogolyubovConstant]
      linarith
    have hh : C₀ * (p + 1) ^ 4 ≤ quarticBogolyubovConstant * (p + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right hCC (by positivity)
    exact hRrank.trans (add_le_add le_rfl hh)
  · intro t ht
    have hprob : |differenceEventProbability A A (A - A) t - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [← differenceEventProbability_eq_triple, zero_add,
        differenceEventProbability_self_zero A hA] using hshift t ht 0
    apply mem_fourfold_difference_of_probability_pos A t
    have h := (abs_le.mp hprob).1
    linarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_sifted_almostPeriods
    (L S B₀ : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 1)
    (hBreg : B₀.IsRankRegular) (hBrank : 1 ≤ B₀.rank)
    (T K : Finset (ZMod N)) (hT : T.Nonempty) (z : ZMod N)
    (hTcard : T.card = B₀.carrier.card) (hTB : ∀ b ∈ T, b - z ∈ B₀.carrier)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M alpha threshold epsilon eta p C : ℝ}
    (hM : 0 < M) (halpha : 1 ≤ alpha) (hthreshold : 0 ≤ threshold)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (q : ℕ) (hq : (q : ℝ) ≤ C * p)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S.carrier, 𝔼 b ∈ T, correlation L.carrier f f (a - b) ^ q)
    (hbad : ∀ a ∈ S.carrier, ∀ b ∈ T, a - b ∉ K → correlation L.carrier f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q)
    (hK : K.card ≤ 2 * S.carrier.card) :
    let D := (3 * C + 1) * p ^ 2
    ∃ A ⊆ S.carrier, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      Real.exp (-D) * S.carrier.card ≤ A.card ∧
      Real.exp (-D) * B₀.carrier.card ≤ B.card ∧
      ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
        R.carrier ⊆ B₀.carrier ∧
        (R.rank : ℝ) ≤ B₀.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
        B₀.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
          (1 + D + Real.log (2 + B₀.rank)))) ≤ R.radius ∧
        1 - epsilon - eta ≤ smoothedDifferenceEventProbability A B K R.carrier := by
  intro D
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hprob⟩ :=
    exists_dense_sets_of_bohr_correlation_moment L hL S.carrier T K S.carrier_nonempty hT
      hSL hkappa f hfsupport hM (by linarith) hthreshold hepsilon hf q hmoment hbad hseparation
  have hdensity := sifting_density_ge_exp_quadratic hM halpha hp hcap q hq
  have hAd : Real.exp (-D) * S.carrier.card ≤ A.card :=
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg S.carrier.card)).trans hAdensity
  have hBd : Real.exp (-D) * B₀.carrier.card ≤ B.card := by
    rw [← hTcard]
    exact (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg T.card)).trans hBdensity
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg hC (sq_nonneg p)]
  obtain ⟨R, hRreg, hRpos, hRwidth, hRB, hRrank, hRlower, hRprob⟩ :=
    exists_difference_event_almostPeriods_with_width S B₀ hBpos hBwidth hBreg hBrank
      A B K z heta heta1 hD (fun b hb => hTB b (hBT hb)) hAd hBd hK
  refine ⟨A, hAS, B, hBT, hA, hB, hAd, hBd, R, hRreg, hRpos, hRwidth,
    hRB, hRrank, hRlower, ?_⟩
  have hprob₀ : 1 - epsilon ≤ differenceEventProbability A B K 0 := by
    simpa only [differenceEventProbability, realSetIndicator, add_zero] using hprob
  have hshift := (abs_le.mp hRprob).1
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

noncomputable def quarticBogolyubovVolumeConstant : ℝ :=
  (quarticBogolyubovConstant + 10) * (quarticBogolyubovConstant + 1)

theorem quarticBogolyubovVolumeConstant_pos : 0 < quarticBogolyubovVolumeConstant := by
  have h := quarticBogolyubovConstant_pos
  unfold quarticBogolyubovVolumeConstant
  positivity

theorem exists_quartic_bogolyubov_with_volume {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius ∧
      Real.exp (-(quarticBogolyubovVolumeConstant * (p + 1) ^ 5)) * N ≤
        (R.carrier.card : ℝ) ∧ R.carrier ⊆ 2 • A - 2 • A := by
  obtain ⟨R, hreg, hpos, hupper, hrank, hwidth, hsub⟩ := exists_quartic_bogolyubov A hp hdensity
  refine ⟨R, hreg, hpos, hupper, hrank, hwidth, ?_, hsub⟩
  exact R.card_lower_bound_of_quartic_rank quarticBogolyubovConstant_pos.le hp
    hpos hupper hrank hwidth

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

noncomputable def quarticBogolyubovProgressionConstant : ℝ :=
  11 * (quarticBogolyubovConstant + 2) ^ 2

theorem quarticBogolyubovProgressionConstant_pos :
    0 < quarticBogolyubovProgressionConstant := by
  have h := quarticBogolyubovConstant_pos
  unfold quarticBogolyubovProgressionConstant
  positivity

theorem exists_quartic_bogolyubov_progression {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ Q : BohrProgression.CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Q.Proper ∧ Q.carrier ⊆ 2 • A - 2 • A ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨B, _hreg, hB, hB1, hrank, hwidth, hsub⟩ := exists_quartic_bogolyubov A hp hdensity
  obtain ⟨Q, hr, hQ, hQB, hcard⟩ := BohrProgression.exists_proper_progression_of_quartic_bounds
    B quarticBogolyubovConstant_pos.le hp hB hB1 hrank hwidth
  exact ⟨Q, hr, hQ, hQB.trans hsub, hcard⟩

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_smoothing_of_large_correlation_at_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c epsilon eta p H : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ epsilon / 2 * (1 + c / 2) ^ q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ S.carrier ∧ C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ z ∈ S.carrier, ∃ A ⊆ S.carrier, ∃ B ⊆ C.carrier.image (fun t => z + t),
        A.Nonempty ∧ B.Nonempty ∧
        Real.exp (-D) * S.carrier.card ≤ A.card ∧ Real.exp (-D) * C.carrier.card ≤ B.card ∧
        ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
          R.carrier ⊆ C.carrier ∧
          (R.rank : ℝ) ≤ C.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
          C.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
            (1 + D + Real.log (2 + C.rank)))) ≤ R.radius ∧
          (1 + c / 4) * (1 - epsilon - eta) ≤
            𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L.carrier f f (a - b + t) := by
  intro D
  obtain ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hsub, z, hz, hmoment, hdiff⟩ :=
    exists_localized_correlation_moment_at_scale L.carrier L.carrier_nonempty S hSpos hSreg
      f hsupport hf hc q hq heven hlarge kappa hkappa0 hscale
  let T := C.carrier.image (fun t => z + t)
  let K := goodDifferenceSet S.carrier T (correlation L.carrier f f) (1 + c / 4)
  have hT : T.Nonempty := C.carrier_nonempty.image _
  have hTcard : T.card = C.carrier.card :=
    Finset.card_image_of_injOn (fun _ _ _ _ h => add_left_cancel h)
  have hTB : ∀ b ∈ T, b - z ∈ C.carrier := by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    simpa only [add_sub_cancel_left] using ht
  have hKcard : K.card ≤ 2 * S.carrier.card :=
    (Finset.card_le_card (goodDifferenceSet_subset _ _ _ _)).trans hdiff
  have hKbad : ∀ a ∈ S.carrier, ∀ b ∈ T, a - b ∉ K →
      correlation L.carrier f f (a - b) ≤ 1 + c / 4 := by
    intro a ha b hb hnot
    exact le_threshold_of_not_mem_goodDifferenceSet ha hb hnot
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  have hkappa := hscale.trans (localizedAverageScale_spec S.rank (pow_nonneg hM.le (2 * q)) hgap).2.1
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max S.rank 1) by omega)
  have hkappa1R : (kappa : ℝ) ≤ 1 := by exact_mod_cast hkappa1
  have hCwidth : C.radius ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hkappa1R S.radius_nonneg
    change C.radius ≤ kappa * S.radius at hhi
    nlinarith
  have hCS : C.carrier ⊆ S.carrier := by
    apply hsub.trans
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := S) hkappa1
  have hCrank : C.rank = S.rank := congrArg Finset.card hfreq
  obtain ⟨A, hAS, B, hBT, hA, hB, hAd, hBd, R, hRreg, hRpos, hRwidth, hRC,
      hRrank, hRlower, hRprob⟩ :=
    exists_sifted_almostPeriods L S C hL hCpos hCwidth hCreg (by omega)
      T K hT z hTcard hTB hSL hkappa₀ f hsupport hM (by linarith) (by linarith)
      hepsilon heta heta1 hp hH hcap hf q hqp hmoment hKbad hseparation hKcard
  refine ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hCS, hsub, z, hz, A, hAS, B, hBT, hA, hB, hAd, hBd,
    R, hRreg, hRpos, hRwidth, hRC, hRrank, hRlower, ?_⟩
  have hmean := smoothed_correlation_ge_of_good_probability L.carrier A B K R.carrier f
    (fun x => (hf x).1) (fun _ hx => le_of_mem_goodDifferenceSet hx)
  exact (mul_le_mul_of_nonneg_left hRprob (by linarith : 0 ≤ 1 + c / 4)).trans hmean

theorem exists_smoothing_of_large_correlation
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c epsilon eta p H : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ epsilon / 2 * (1 + c / 2) ^ q) :
    let kappa := localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q)
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ S.carrier ∧
      ∃ z ∈ S.carrier, ∃ A ⊆ S.carrier, ∃ B ⊆ C.carrier.image (fun t => z + t),
        A.Nonempty ∧ B.Nonempty ∧
        Real.exp (-D) * S.carrier.card ≤ A.card ∧ Real.exp (-D) * C.carrier.card ≤ B.card ∧
        ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
          R.carrier ⊆ C.carrier ∧
          (R.rank : ℝ) ≤ C.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
          C.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
            (1 + D + Real.log (2 + C.rank)))) ≤ R.radius ∧
          (1 + c / 4) * (1 - epsilon - eta) ≤
            𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L.carrier f f (a - b + t) := by
  intro kappa D
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  obtain ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hCS, _, hrest⟩ :=
    exists_smoothing_of_large_correlation_at_scale L S hL hSpos hSwidth hSreg hSrank
      hSL hkappa₀ f hsupport hM hc hepsilon heta heta1 hp hH hcap hf q hq heven hqp
      hlarge hseparation kappa
      (localizedAverageScale_spec S.rank (pow_nonneg hM.le _) hgap).1 le_rfl
  exact ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hCS, hrest⟩

end Erdos3.LocalConvolution

end

end OAI
