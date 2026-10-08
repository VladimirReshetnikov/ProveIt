/-
Modified for ProveIt: retain only the quantitative-density source construction.
Omit the logarithmic/reciprocal-sum corollaries and the combined manuscript
conclusion; the Gowers Theorem 1.3 bridge needs QuantitativeDensityTheorem only.
Pinned source and copyright status: ../../../../../LICENSE.provenance.
-/
import OAI.Combinatorics.Progressions.Dynamics.AmplificationSourceResourceBudget
import OAI.Combinatorics.Progressions.Dynamics.RelativePatchAmplificationIteration
import OAI.Combinatorics.Progressions.Lattices.IntervalIntegerVectorAPFree
import OAI.Combinatorics.Progressions.Linear.AmplificationSourceRankBudget
import OAI.Combinatorics.Progressions.Linear.RelativeRankZeroSource
import OAI.Combinatorics.Progressions.Probability.DensityBoundFromInvariant
import OAI.Combinatorics.Progressions.Sampling.ScoredPatchDensityStep

namespace OAI

section

namespace Erdos3
open Filter

theorem eventually_quarter_resource_paid {β A D : ℝ}
    (hβ : (1 / 4 : ℝ) < β) (hA : 0 < A) (hD : 0 ≤ D) :
    ∀ᶠ p : ℝ in atTop, D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A * p ^ β := by
  rcases eq_or_lt_of_le hD with hD | hD
  · have hD0 : D = 0 := hD.symm
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp
    rw [hD0, zero_mul, zero_mul]
    exact mul_nonneg hA.le (Real.rpow_nonneg hp β)
  · exact eventually_rpow_log_le hβ hA hD

theorem source_scaled_exponential_room {U N L C factor : ℝ}
    (hU : 0 < U) (hN : 1 < N) (hfactor : 0 < factor)
    (hlogU : Real.log U ≤ L) (hroom : L + C ≤ Real.log (Real.log N))
    (hreserve : Real.log factor ≤ C) :
    factor * U ≤ Real.log N ∧ Real.exp (factor * U) ≤ N := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hbound : factor * U ≤ Real.log N := by
    apply (Real.log_le_log_iff (mul_pos hfactor hU) hlogN).mp
    rw [Real.log_mul hfactor.ne' hU.ne']
    linarith
  exact ⟨hbound, (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log (by linarith))⟩

theorem source_exponential_room {U N L C : ℝ}
    (hU : 0 < U) (hN : 1 < N) (hlogU : Real.log U ≤ L)
    (hroom : L + C ≤ Real.log (Real.log N)) (hreserve : 0 ≤ C) :
    U ≤ Real.log N ∧ Real.exp U ≤ N := by
  simpa only [one_mul] using source_scaled_exponential_room hU hN zero_lt_one
    hlogU hroom (by simpa only [Real.log_one] using hreserve)

theorem source_half_log_room {U N L C : ℝ}
    (hU : 0 < U) (hN : 1 < N) (hlogU : Real.log U ≤ L)
    (hroom : L + C ≤ Real.log (Real.log N)) (hreserve : Real.log 2 ≤ C) :
    2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
  obtain ⟨hbound, _hexp⟩ := source_scaled_exponential_room hU hN (by norm_num : (0 : ℝ) < 2)
    hlogU hroom hreserve
  refine ⟨hbound, ?_, by linarith⟩
  exact (Real.exp_le_exp.mpr (show U ≤ Real.log N by linarith)).trans_eq
    (Real.exp_log (by linarith))

theorem eventually_source_exponential_room {β A D : ℝ}
    (hβ : (1 / 4 : ℝ) < β) (hA : 0 < A) (hD : 0 ≤ D) :
    ∀ᶠ p : ℝ in atTop, ∀ U N C : ℝ,
      0 < U → 1 < N → Real.log 2 ≤ C →
      Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
      A * p ^ β + C ≤ Real.log (Real.log N) →
      2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
  filter_upwards [eventually_quarter_resource_paid hβ hA hD] with p hpaid
  intro U N C hU hN hreserve hlogU hinvariant
  exact source_half_log_room hU hN (hlogU.trans hpaid) hinvariant hreserve

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped BigOperators

theorem subquadratic_patch_descent (s : ℕ) {κ H₀ K q A₀ B D : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A₀) (hB : 0 < B) (hD : 0 < D) :
    let μ := levelCoefficient K * Real.log q
    let ν := gainExponent K
    let β := 1 - (ν - μ) / 2
    ∃ c p₀ Cmin : ℝ, 0 < c ∧ 0 ≤ Cmin ∧
      ∀ C₀ : ℝ, Cmin ≤ C₀ → ∀ p : ℝ, p₀ ≤ p → ∀ (d N M a₀ q₀ : ℕ) (U : ℝ)
        (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ B * p ^ μ * Real.log (2 + p) →
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
        A₀ * p ^ β + C₀ ≤ Real.log (Real.log N) →
        let α := 𝔼 n : Fin N, f n.val
        let G := κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2
        0 < α → densityParameter α = p →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - G * α) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q' a len : ℕ, 0 < q' ∧ 1 < len ∧ (∀ n < len, a + q' * n < N) ∧
          0 < (𝔼 n : Fin len, f (a + q' * n.val)) ∧
          let p' := densityParameter (𝔼 n : Fin len, f (a + q' * n.val))
          p' ≤ p - c * p ^ ν ∧ p' + 1 ≤ p ∧
            A₀ * p' ^ β + C₀ ≤ Real.log (Real.log len) := by
  intro μ ν β
  obtain ⟨C, P, hC, hP, hstep⟩ := scored_patch_density_step s
  obtain ⟨c, hc, hdrop⟩ := exists_selected_density_drop hκ hH hK
  let Cmin := max 0 (Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)))
  have hCmin : 0 ≤ Cmin := le_max_left _ _
  have hbase : Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) ≤ Cmin := le_max_right _ _
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hL : 0 ≤ Real.log (4 * (P : ℝ)) := Real.log_nonneg (by linarith)
  have hbudgets := subquadratic_patch_iteration_budgets hK hq hq2 hA hc hB hD hL (2 * s * s)
  have hν : 0 < ν := (gainExponent_pos_le_quarter hK).1
  have hlarge := (tendsto_rpow_atTop hν).eventually_ge_atTop (1 / c)
  have hall : ∀ᶠ p : ℝ in atTop, 1 ≤ p ∧
      ((2 * s * s + 1 : ℕ) * B * p ^ μ * Real.log (2 + p) +
        D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A₀ * p ^ β) ∧
      (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * B * p ^ μ * Real.log (2 + p) ≤
        A₀ * (β * c * p ^ (β + ν - 1))) ∧
      (c * p ^ ν ≤ Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2)) ∧
      2 ≤ p - c * p ^ ν ∧ 1 ≤ c * p ^ ν := by
    filter_upwards [hbudgets, hdrop, hlarge, eventually_ge_atTop (1 : ℝ)] with p hbud hd hu hp
    refine ⟨hp, hbud.1, hbud.2, hd.1, hd.2, ?_⟩
    have h := (div_le_iff₀ hc).mp hu
    simpa only [mul_comm] using h
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp hall
  refine ⟨c, p₀, Cmin, hc, hCmin, ?_⟩
  intro C₀ hreserve p hp d N M a₀ q₀ U A f hN hq₀ hslice hf hU hM hLip hRank hResource hinvariant α G hα hpα hscore
  obtain ⟨hp1, hfit, hpaid, hgain, hroom, hunit⟩ := hp₀ p hp
  have hp0 : 0 < p := by linarith
  let R := B * p ^ μ * Real.log (2 + p)
  let V := D * p ^ (1 / 4 : ℝ) * Real.log (2 + p)
  have hsize : Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) +
      (2 * s * s + 1 : ℕ) * R + V ≤ Real.log (Real.log N) := by
    have hfit' : (2 * s * s + 1 : ℕ) * R + V ≤ A₀ * p ^ β := by
      simpa only [R, V, mul_assoc] using hfit
    linarith
  have hH0 : 0 < H₀ := by nlinarith
  have hG : 0 < G := div_pos (mul_pos hκ (amplificationGain_pos hκ hH0 _)) (by norm_num)
  have hpmean : densityParameter (𝔼 n : Fin N, f n.val) = p := hpα
  obtain ⟨q', a, len, hq', hlen, hin, hloss, hdense, hparam⟩ :=
    hstep d N M a₀ q₀ U R V G (c * p ^ ν) A f hN hq₀ hslice hf hU hM hLip
      hRank hResource hsize hα hG hgain (by simpa only [hpmean] using hroom) hscore
  rw [hpmean] at hparam
  refine ⟨q', a, len, hq', hlen, hin, (mul_pos hG hα).trans hdense, hparam, by linarith, ?_⟩
  obtain ⟨_, _, _, _, hβ, hβ1, _⟩ := subquadratic_rank_exponents hK hq hq2
  apply density_invariant_with_general_loss hp0
    ((by norm_num : (0 : ℝ) ≤ 2).trans (densityParameter_ge_two _))
    (by linarith) hβ1.le hA.le hinvariant hparam hloss
  simpa only [R, mul_assoc] using hpaid

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def SubquadraticPatchSource (k s : ℕ) (κ H₀ K q A₀ B D pmin Csrc : ℝ) : Prop :=
  let μ := levelCoefficient K * Real.log q
  let β := 1 - (gainExponent K - μ) / 2
  ∀ S : APFreeInterval k, pmin ≤ S.parameter →
    A₀ * S.parameter ^ β + Csrc ≤ Real.log (Real.log S.length) →
    ∃ (d M a q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d),
      0 < q₀ ∧ (∀ n < M, a + q₀ * n < S.length) ∧ 1 ≤ U ∧
      Real.log S.length - U ≤ Real.log M ∧ (A.kernel.lip : ℝ) + 1 ≤ Real.exp U ∧
      Real.log ((d : ℝ) + 1) ≤ B * S.parameter ^ μ * Real.log (2 + S.parameter) ∧
      Real.log U ≤ D * S.parameter ^ (1 / 4 : ℝ) * Real.log (2 + S.parameter) ∧
      let G := κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log S.parameter⌋₊ / 2
      Real.exp (-U) ≤ (𝔼 n : Fin M,
        (intervalIndicator S.points (a + q₀ * n.val) - G * S.density) *
          A.value (fun _ => (n.val : ℝ)))

theorem quantitative_density_of_patch_source {k s : ℕ} (hk : 0 < k)
    {κ H₀ K q A₀ B D pmin Csrc : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A₀) (hB : 0 < B) (hD : 0 < D)
    (hsource : SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc) :
    QuantitativeDensityBound k := by
  let μ := levelCoefficient K * Real.log q
  let ν := gainExponent K
  let β := 1 - (ν - μ) / 2
  obtain ⟨c, p₀, Cdesc, _, _, hdesc⟩ := subquadratic_patch_descent s hκ hH hK hq hq2 hA hB hD
  let T := max pmin p₀
  obtain ⟨C₀, hC₀, _, hclosed⟩ := no_interval_invariant_of_descent k T (max Csrc Cdesc)
  have hCsrc : Csrc ≤ C₀ := (le_max_left _ _).trans hC₀
  have hCdesc : Cdesc ≤ C₀ := (le_max_right _ _).trans hC₀
  obtain ⟨_, _, _, _, hβ, hβ1, _⟩ := subquadratic_rank_exponents hK hq hq2
  apply quantitative_density_of_no_invariant hk hA (by dsimp [β, ν, μ]; linarith : 0 < β) hβ1
  apply hclosed A₀ β hA.le
  intro S hinvariant hlarge
  have hpmin : pmin ≤ S.parameter := (le_max_left _ _).trans hlarge.le
  have hp₀ : p₀ ≤ S.parameter := (le_max_right _ _).trans hlarge.le
  have hsourceSize : A₀ * S.parameter ^ β + Csrc ≤ Real.log (Real.log S.length) := by linarith
  obtain ⟨d, M, a, q₀, U, A, hq₀, hslice, hU, hM, hLip, hRank, hResource, hscore⟩ :=
    hsource S hpmin hsourceSize
  have hmean : (𝔼 n : Fin S.length, intervalIndicator S.points n.val) = S.density :=
    mean_intervalIndicator S.subset
  have hpositive : 0 < (𝔼 n : Fin S.length, intervalIndicator S.points n.val) := by
    rw [hmean]
    exact S.density_pos
  have hpmean : densityParameter (𝔼 n : Fin S.length, intervalIndicator S.points n.val) = S.parameter :=
    congrArg densityParameter hmean
  have hscore' : Real.exp (-U) ≤ (𝔼 n : Fin M,
      (intervalIndicator S.points (a + q₀ * n.val) -
        (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log S.parameter⌋₊ / 2) *
          (𝔼 j : Fin S.length, intervalIndicator S.points j.val)) * A.value (fun _ => (n.val : ℝ))) := by
    simpa only [hmean] using hscore
  obtain ⟨q', a', len, hq', hlen, _, hnewpos, _, hunit, hnewinv⟩ :=
    hdesc C₀ hCdesc S.parameter hp₀ d S.length M a q₀ U A (intervalIndicator S.points)
      S.length_gt_one hq₀ hslice (fun n _ => intervalIndicator_mem_Icc S.points n)
      hU hM hLip hRank hResource hinvariant hpositive hpmean hscore'
  have hnewmean := mean_progression_indicator S.points a' q' len
  have hpos : 0 < intervalDensity len (progressionPreimage S.points a' q' len) := by
    rw [← hnewmean]
    exact hnewpos
  let S' := S.reindex a' q' len hq' hlen hpos
  refine ⟨S', ?_, ?_⟩
  · change A₀ * densityParameter (intervalDensity len (progressionPreimage S.points a' q' len)) ^ β + C₀ ≤
      Real.log (Real.log len)
    rw [← hnewmean]
    exact hnewinv
  · change densityParameter (intervalDensity len (progressionPreimage S.points a' q' len)) + 1 ≤ S.parameter
    rw [← hnewmean]
    exact hunit

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSliceScore_interval {k s d q : ℕ} (S : APFreeInterval k)
    (slice : ResidueBoxSlice (fun _ : Unit => S.length) q)
    (A : PolynomialPatch Unit s d) (target : ℝ) :
    relativePatchSliceScore slice S.integerIndicator target A =
      𝔼 n : Fin (slice.length ()),
        (intervalIndicator S.points (slice.start () + q * n.val) - target) *
          A.value (fun _ => (n.val : ℝ)) := by
  unfold relativePatchSliceScore
  let : DecidableEq Unit := Classical.decEq _
  apply Fintype.expect_equiv (Equiv.piUnique (fun i => Fin (slice.length i)))
  intro u
  simp only [APFreeInterval.integerIndicator, ResidueBoxSlice.point, Int.toNat_natCast]
  congr 2

theorem APFreeInterval.patch_of_relative_absolute {s n₀ E d₀ : ℕ} {τ p Λ : ℝ}
    (S : APFreeInterval (s + 2))
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ S.density / 2)
    (haΛ : S.density / 2 ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p (S.density / 2) Λ d₀)
    (hN : Real.exp ((p + 2) ^ E) ≤ (S.length : ℝ)) :
    ∃ (d M a q : ℕ) (A : PolynomialPatch Unit s d),
      0 < q ∧ (∀ n < M, a + q * n < S.length) ∧ 0 < M ∧ d ≤ d₀ ∧
      Real.log S.length - (p + 2) ^ E ≤ Real.log M ∧
      (A.kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ E) ∧
      Real.exp (-((p + 2) ^ E)) ≤
        𝔼 n : Fin M,
          (intervalIndicator S.points (a + q * n.val) - (1 - τ) ^ (s + 1) * Λ) *
            A.value (fun _ => (n.val : ℝ)) := by
  have hmean : 2 * (S.density / 2) ≤
      𝔼 x ∈ integerBox (fun _ : Unit => S.length), S.integerIndicator x := by
    rw [S.integerIndicator_mean]
    linarith
  obtain ⟨q, hq, slice, d, A, hlength, hd, hcomplexity, hscore⟩ :=
    hrelative.of_mean_increment hp ha haΛ hΛ habsolute Unit
      (by simpa using (by linarith : (1 : ℝ) ≤ p)) (fun _ => S.length) (fun _ => hN)
      S.integerIndicator (fun x _ => S.integerIndicator_mem_Icc x)
      (S.integerIndicator_apFree (by omega)) hmean
  obtain ⟨hM, hlog⟩ := log_length_lower_of_exp_slice (N := S.length) (M := slice.length ())
    (by have := S.length_gt_one; omega)
    (hlength ())
  refine ⟨d, slice.length (), slice.start (), q, A, hq, slice.inside (), hM, hd, hlog,
    relativePatchComplexity_kernel_bound A hcomplexity, ?_⟩
  rwa [relativePatchSliceScore_interval] at hscore

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem subquadratic_patch_source_of_relative_family
    {s n₀ C E : ℕ} {τ H₀ : ℝ}
    (hC : 1 ≤ C) (hE : 2 ≤ E)
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hκ : 0 < (1 - τ) ^ (s + 1)) (hκ1 : (1 - τ) ^ (s + 1) < 1)
    (hH : 1 < H₀) (hκH : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H₀)
    (hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p
        (amplificationGain ((1 - τ) ^ (s + 1)) H₀ j)
        ((s + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
        (amplificationResource p (C + 1) (E + 1) j)) :
    ∃ pmin : ℝ, SubquadraticPatchSource (s + 2) s
      ((1 - τ) ^ (s + 1)) H₀ (E + 1) 1 1
      (amplificationSourceRankLogConstant (s + 1) C (E + 1))
      (amplificationSourceLogCoefficient (C + 1) E) pmin (Real.log 2) := by
  let κ := (1 - τ) ^ (s + 1)
  let K : ℝ := E + 1
  let B := amplificationSourceRankLogConstant (s + 1) C K
  let D := amplificationSourceLogCoefficient (C + 1) E
  have hK : 2 ≤ K := by dsimp [K]; exact_mod_cast (show 2 ≤ E + 1 by omega)
  have hD : 0 < D := amplificationSourceLogCoefficient_pos _ (by omega)
  have hβ : (1 / 4 : ℝ) < potentialExponent K := (potentialExponent_bounds hK).1
  have hlow := eventually_low_density_at_selected_level hκ hκ1.le hH.le hK
  have hroom := eventually_source_exponential_room hβ (by norm_num : (0 : ℝ) < 1) hD.le
  have hev : ∀ᶠ p : ℝ in atTop,
      LowDensityThreshold (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊)
        (Real.exp (-p)) ∧ 3 ≤ p ∧ (n₀ : ℝ) ≤ p ∧
      ∀ U N Csrc : ℝ, 0 < U → 1 < N → Real.log 2 ≤ Csrc →
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
        1 * p ^ potentialExponent K + Csrc ≤ Real.log (Real.log N) →
        2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
    filter_upwards [hlow, hroom, eventually_ge_atTop (3 : ℝ),
      eventually_ge_atTop (n₀ : ℝ)] with p hl hr hp hn
    exact ⟨hl, hp, hn, hr⟩
  obtain ⟨pmin, hpmin⟩ := eventually_atTop.mp hev
  refine ⟨pmin, ?_⟩
  intro S hlarge hinvariant
  let p := S.parameter
  let j := ⌊levelCoefficient K * Real.log p⌋₊
  let Pj := amplificationResource p (C + 1) (E + 1) j
  let U := (2 + Pj) ^ E
  obtain ⟨hl, hp3, hn, hr⟩ := hpmin p hlarge
  have hp : 2 ≤ p := by linarith
  have hparam : p ≤ Pj := amplificationResource_parameter_le hp (by omega) (by omega) j
  have hP : 2 ≤ Pj := hp.trans hparam
  have hα : Real.exp (-p) = S.density / 2 :=
    S.exp_neg_parameter_eq_half (by dsimp only [p] at hp3; linarith)
  have hU : 1 ≤ U ∧ Pj ≤ U ∧ 0 < U ∧
      Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one, U, Pj, j, K, D] using
        amplificationSource_final_cost_spec (D := C + 1) (K := E + 1) (E := E)
          hp (by omega) (by omega) (by omega)
  have hinvariant' : 1 * p ^ potentialExponent K + Real.log 2 ≤
      Real.log (Real.log (S.length : ℝ)) := by
    simpa only [Real.log_one, mul_zero, sub_zero, potentialExponent] using hinvariant
  have hN : Real.exp U ≤ (S.length : ℝ) :=
    (hr U S.length (Real.log 2) hU.2.2.1
      (by exact_mod_cast S.length_gt_one) le_rfl hU.2.2.2 hinvariant').2.1
  have hgain := (amplificationGain_low_density_parameters hκ hκ1 hH hκH j).1
  have habsolute := hfamily p hp hn j (Real.exp (-p)) le_rfl hl
  rw [hα] at habsolute
  have hraw : amplificationGain κ H₀ j * (S.density / 2) ≤ 1 := by
    simpa only [hα] using (hl.raw_target_lt_one hgain).le
  have haΛ : S.density / 2 ≤ amplificationGain κ H₀ j * (S.density / 2) := by
    nlinarith [S.density_pos]
  obtain ⟨d, M, a, q, A, hq, hinside, _hM, hd, hlength, hLip, hscore⟩ :=
    S.patch_of_relative_absolute hrelative hP
      ((Real.exp_le_exp.mpr (neg_le_neg hparam)).trans_eq hα)
      haΛ hraw habsolute (by simpa only [add_comm Pj 2] using hN)
  refine ⟨d, M, a, q, U, A, hq, hinside, hU.1, ?_, ?_, ?_, hU.2.2.2, ?_⟩
  · simpa only [U, add_comm Pj 2] using hlength
  · simpa only [U, add_comm Pj 2] using hLip
  · apply log_linear_amplification_rank_source (by omega : 1 ≤ s + 1)
      (by linarith : 1 < K) hp
    simpa only [j, add_comm p 2] using hd
  · have htarget : κ * amplificationGain κ H₀ j * (S.density / 2) =
        (κ * amplificationGain κ H₀ j / 2) * S.density := by ring
    have hscore' : Real.exp (-U) ≤ 𝔼 n : Fin M,
        (intervalIndicator S.points (a + q * n.val) -
          κ * amplificationGain κ H₀ j * (S.density / 2)) *
          A.value (fun _ => (n.val : ℝ)) := by
      simpa only [U, add_comm Pj 2, mul_assoc] using hscore
    rw [htarget] at hscore'
    exact hscore'

theorem exists_subquadratic_patch_source_of_uniform_relative_lifting
    (s n₀ : ℕ) [NeZero n₀] (hs : 1 ≤ s)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule s n₀ s τ E) :
    ∃ κ H₀ K B D pmin : ℝ,
      0 < κ ∧ 1 < κ * H₀ ∧ 2 ≤ K ∧ 0 < B ∧ 0 < D ∧
      SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (Real.log 2) := by
  obtain ⟨C, hC, xi, hxi, hinitial⟩ :=
    exists_initial_relative_absolute_rule n₀ (s + 2) (by omega)
  have hH : 1 < 1 + xi := by linarith
  obtain ⟨τ, hτ, hτhalf, hκ, hκ1, hκgain, hκH⟩ :=
    exists_relative_amplification_discount s hH
  obtain ⟨E, hE, hrelative⟩ := hlifting τ hτ hτhalf
  have hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p
        (amplificationGain ((1 - τ) ^ (s + 1)) (1 + xi) j)
        ((s + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
        (amplificationResource p (C + 1) (E + 1) j) := by
    intro p hp hn j
    apply LowDensityRelativeAbsoluteRule.iterate hrelative hp (by omega)
      (hn.trans (amplificationResource_parameter_le_zero (K := E + 1) hp (by omega)))
      hκ hκ1 hH hκH _ j
    intro a ha _
    simpa only [Nat.add_sub_cancel, add_comm (2 : ℝ) p] using hinitial hp ha
  obtain ⟨pmin, hsource⟩ := subquadratic_patch_source_of_relative_family
    (by omega : 1 ≤ C) hE hrelative hκ hκ1 hH hκH hfamily
  refine ⟨(1 - τ) ^ (s + 1), 1 + xi, (E + 1 : ℕ),
    amplificationSourceRankLogConstant (s + 1) C (E + 1),
    amplificationSourceLogCoefficient (C + 1) E, pmin, hκ, hκgain,
    ?_, ?_, amplificationSourceLogCoefficient_pos _ (by omega), ?_⟩
  · exact_mod_cast (show 2 ≤ E + 1 by omega)
  · exact amplificationSourceRankLogConstant_pos (by omega) (by exact_mod_cast (show 1 < E + 1 by omega))
  · simpa only [Nat.cast_add, Nat.cast_one] using hsource

theorem quantitative_density_bound_of_uniform_relative_lifting
    (k n₀ : ℕ) [NeZero n₀] (hk : 3 ≤ k)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule (k - 2) n₀ (k - 2) τ E) :
    QuantitativeDensityBound k := by
  obtain ⟨κ, H₀, K, B, D, pmin, hκ, hgain, hK, hB, hD, hsource⟩ :=
    exists_subquadratic_patch_source_of_uniform_relative_lifting (k - 2) n₀ (by omega) hlifting
  have hresult := quantitative_density_of_patch_source (by omega : 0 < (k - 2) + 2)
    hκ hgain hK (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1) hB hD hsource
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hresult

end Erdos3

end

end OAI
