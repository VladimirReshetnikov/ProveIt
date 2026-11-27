import GRHArticle.ProgressionFree.IntegerLargestPrimePastingDensity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.PSeries

/-!
# An elementary uniform dilation estimate for smooth numbers

Möbius inversion on the rough part expresses the smooth count as a weighted
sum of floors. When two cutoffs are comparable, the error is controlled by
the number of rough divisors of the larger cutoff. The density of these rough
integers can be made arbitrarily small by increasing the smooth cutoff.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

private theorem rough_divisor {Y d n : ℕ} (hn : n ∈ integerRoughNumbers Y) (hd : d ∣ n) :
    d ∈ integerRoughNumbers Y := by
  have hd₀ : d ≠ 0 := fun he ↦ hn.1 (Nat.zero_dvd.mp (he ▸ hd))
  exact ⟨hd₀, fun p hp ↦ hn.2 p
    ((Nat.mem_primeFactorsList_iff_dvd hn.1 (Nat.prime_of_mem_primeFactorsList hp)).mpr
      ((Nat.dvd_of_mem_primeFactorsList hp).trans hd))⟩

private theorem rough_coprime_smooth {Y d s : ℕ} (hd : d ∈ integerRoughNumbers Y)
    (hs : s ∈ Nat.smoothNumbers (Y+1)) : d.Coprime s := by
  by_contra hn
  obtain ⟨p, hp, hpd, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hlarge := hd.2 p ((Nat.mem_primeFactorsList_iff_dvd hd.1 hp).mpr hpd)
  have hsmall := Nat.mem_smoothNumbers'.mp hs p hp hps
  omega

private theorem filter_divisors_eq_roughPart_divisors (Y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter (· ∈ integerRoughNumbers Y)) = (integerRoughPart Y n).divisors := by
  classical
  have hprod := integerSmoothPart_mul_roughPart Y hn
  have hr := integerRoughPart_mem Y n
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, hdR⟩
    refine ⟨(rough_coprime_smooth hdR (integerSmoothPart_mem Y n)).dvd_of_dvd_mul_left ?_, hr.1⟩
    exact hprod.symm ▸ hd
  · rintro ⟨hd, _⟩
    have hd' : integerRoughPart Y n ∣ n := by
      calc
        integerRoughPart Y n ∣ integerSmoothPart Y n * integerRoughPart Y n := dvd_mul_left _ _
        _ = n := hprod
    exact ⟨⟨hd.trans hd', hn⟩, rough_divisor hr hd⟩

private theorem roughPart_eq_one_iff (Y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    integerRoughPart Y n = 1 ↔ n ∈ Nat.smoothNumbers (Y+1) := by
  constructor
  · intro h
    have he := integerSmoothPart_mul_roughPart Y hn
    rw [h, mul_one] at he
    exact he ▸ integerSmoothPart_mem Y n
  · intro hs
    have h1 : 1 ∈ integerRoughNumbers Y := ⟨one_ne_zero, fun p hp ↦ by simp at hp⟩
    simpa only [one_mul] using integerRoughPart_mul_of_parts h1 hs

private theorem sum_moebius_roughDivisors (Y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors.filter (· ∈ integerRoughNumbers Y), (μ d : ℝ)) =
      if n ∈ Nat.smoothNumbers (Y+1) then 1 else 0 := by
  classical
  have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f (integerRoughPart Y n))
    ArithmeticFunction.coe_zeta_mul_moebius
  change ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * μ)
    (integerRoughPart Y n) = _ at h
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at h
  rw [filter_divisors_eq_roughPart_divisors Y hn]
  have he := roughPart_eq_one_iff Y hn
  by_cases hs : n ∈ Nat.smoothNumbers (Y+1)
  · rw [if_pos (he.mpr hs)] at h
    rw [if_pos hs]
    exact_mod_cast h
  · rw [if_neg (mt he.mp hs)] at h
    rw [if_neg hs]
    exact_mod_cast h

/-- Smooth numbers counted by inclusion-exclusion over rough divisors, with any
common divisor cutoff at least as large as the counting cutoff. -/
theorem countUpTo_smooth_eq_sum_moebius (Y : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    (countUpTo (Nat.smoothNumbers (Y+1)) M : ℝ) =
      ∑ d ∈ integerPrefixSlice (integerRoughNumbers Y) N, (μ d : ℝ) * ((M/d : ℕ) : ℝ) := by
  classical
  let D := integerPrefixSlice (integerRoughNumbers Y) N
  have hD (n : ℕ) (hn : n ∈ Icc 1 M) :
      n.divisors.filter (· ∈ integerRoughNumbers Y) = D.filter (· ∣ n) := by
    have hn0 := Nat.ne_of_gt (mem_Icc.mp hn).1
    ext d
    simp only [D, integerPrefixSlice, integerPrefix, mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hdR⟩
      exact ⟨⟨⟨Nat.pos_of_ne_zero hdR.1,
        (Nat.le_of_dvd (mem_Icc.mp hn).1 hd).trans ((mem_Icc.mp hn).2.trans hMN)⟩, hdR⟩, hd⟩
    · rintro ⟨⟨_, hdR⟩, hd⟩
      exact ⟨⟨hd, hn0⟩, hdR⟩
  calc
    (countUpTo (Nat.smoothNumbers (Y+1)) M : ℝ) =
        ∑ n ∈ Icc 1 M, (if n ∈ Nat.smoothNumbers (Y+1) then 1 else 0) := by
      rw [← sum_filter]
      change ((integerPrefixSlice (Nat.smoothNumbers (Y+1)) M).card : ℝ) = _
      rw [sum_const, nsmul_eq_mul, mul_one]
      have he : integerPrefixSlice (Nat.smoothNumbers (Y+1)) M =
          (Icc 1 M).filter (fun n ↦ n ∈ Nat.smoothNumbers (Y+1)) := by
        ext n
        simp only [integerPrefixSlice, integerPrefix, mem_filter]
      rw [he]
    _ = ∑ n ∈ Icc 1 M, ∑ d ∈ D, (if d ∣ n then (μ d : ℝ) else 0) := by
      apply sum_congr rfl
      intro n hn
      rw [← sum_filter, ← hD n hn, sum_moebius_roughDivisors Y (Nat.ne_of_gt (mem_Icc.mp hn).1)]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      have hdR : d ∈ integerRoughNumbers Y := by
        have hmem : d ∈ integerPrefix (N) ∧ d ∈ integerRoughNumbers Y := by
          simpa only [D, integerPrefixSlice, mem_filter] using hd
        exact hmem.2
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      congr 1
      have he := countUpTo_dvd d M (Nat.pos_of_ne_zero hdR.1)
      have he' : countUpTo {n | d ∣ n} M = ((Icc 1 M).filter (fun n ↦ d ∣ n)).card := by
        unfold countUpTo
        exact congrArg Finset.card (Finset.ext fun n ↦ by simp only [mem_filter, Set.mem_setOf_eq])
      rw [← he', he]

private theorem normalized_div_error {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    |((N/d : ℕ) : ℝ) / N - 1/(d : ℝ)| ≤ 1/(N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : ((N/d : ℕ) : ℝ)/N ≤ 1/(d : ℝ) :=
    (div_le_div_iff₀ hNr hdr).mpr (by
      rw [one_mul]
      exact_mod_cast Nat.div_mul_le_self N d)
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  apply sub_le_iff_le_add.mpr
  rw [← add_div]
  apply (div_le_div_iff₀ hdr hNr).mpr
  rw [one_mul]
  have h : N ≤ (N/d+1)*d := by
    have he := Nat.mod_add_div N d
    have hmod := (Nat.mod_lt N hd).le
    rw [Nat.add_mul, one_mul, Nat.mul_comm (N/d) d]
    omega
  exact_mod_cast (show N ≤ (1+N/d)*d by simpa only [add_comm] using h)

private theorem densityUpTo_smooth_dilation_le (Y : ℕ) {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    |densityUpTo (Nat.smoothNumbers (Y+1)) M - densityUpTo (Nat.smoothNumbers (Y+1)) N| ≤
      densityUpTo (integerRoughNumbers Y) N * (1 + (N : ℝ)/M) := by
  classical
  have hN := hM.trans_le hMN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  let D := integerPrefixSlice (integerRoughNumbers Y) N
  unfold densityUpTo
  rw [countUpTo_smooth_eq_sum_moebius Y hMN, countUpTo_smooth_eq_sum_moebius Y le_rfl,
    sum_div, sum_div, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ D, (1/(N : ℝ)+1/(M : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := by
        have h : 1 ≤ d ∧ d ≤ N ∧ d ∈ integerRoughNumbers Y := by
          simpa only [D, integerPrefixSlice, mem_filter, integerPrefix, mem_Icc, and_assoc] using hd
        exact h.1
      rw [mul_div_assoc, mul_div_assoc, ← mul_sub, abs_mul]
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      refine (mul_le_of_le_one_left (abs_nonneg _) hμ).trans ?_
      have htri := abs_sub_le (((M/d : ℕ) : ℝ) / M) (1/(d : ℝ)) (((N/d : ℕ) : ℝ) / N)
      rw [abs_sub_comm (1/(d : ℝ))] at htri
      linarith [normalized_div_error hM hd0, normalized_div_error hN hd0]
    _ = _ := by
      change _ = (D.card : ℝ) / (N : ℝ) * (1 + (N : ℝ)/M)
      rw [sum_const, nsmul_eq_mul]
      field_simp

/-- The asymptotic density of rough numbers tends to zero with the prime cutoff. -/
theorem tendsto_integerSmoothDensityFactor_zero :
    Tendsto integerSmoothDensityFactor atTop (𝓝 0) := by
  classical
  have hl (Y : ℕ) : (∑ i ∈ range Y, (1/(i+1) : ℝ)) ≤ (integerSmoothDensityFactor Y)⁻¹ := by
    let e : {i // i ∈ range Y} ↪ Nat.smoothNumbers (Y+1) := {
      toFun i := ⟨i.val + 1, by
        refine ⟨Nat.succ_ne_zero _, fun p hp ↦ ?_⟩
        have hY := mem_range.mp i.property
        have hp' := Nat.le_of_mem_primeFactorsList hp
        omega⟩
      inj' := fun i j h ↦ Subtype.ext (Nat.add_right_cancel (congrArg Subtype.val h)) }
    have hsum := hasSum_reciprocal_smoothNumbers Y
    have h := hsum.summable.sum_le_tsum ((range Y).attach.map e) (fun _ _ ↦ by positivity)
    rw [hsum.tsum_eq, sum_map] at h
    change (∑ i ∈ (range Y).attach, ((i.val+1 : ℕ) : ℝ)⁻¹) ≤ _ at h
    rw [sum_attach (range Y) (fun i : ℕ ↦ ((i+1 : ℕ) : ℝ)⁻¹)] at h
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using h
  have h := tendsto_atTop_mono hl Real.tendsto_sum_range_one_div_nat_succ_atTop
  simpa only [Function.comp_def, inv_inv] using tendsto_inv_atTop_zero.comp h

/-- Dilating the counting cutoff by a fixed positive integer changes the
smooth-number proportion by a term tending to zero uniformly in the smooth
cutoff. This uses only Möbius inversion and the elementary rough density. -/
theorem eventually_abs_densityUpTo_smooth_div_sub_lt {a : ℕ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ Y : ℕ,
      |densityUpTo (Nat.smoothNumbers (Y+1)) (N/a) -
        densityUpTo (Nat.smoothNumbers (Y+1)) N| < ε := by
  let C := (2:ℝ)*a + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < ε / C := div_pos hε hC
  have hfactor := (tendsto_integerSmoothDensityFactor_zero.eventually_lt_const hδ)
  obtain ⟨K, hK⟩ := hfactor.exists
  have hrough := (hasNaturalDensity_integerRoughNumbers K).eventually_lt_const hK
  have hsmooth : HasNaturalDensity (Nat.smoothNumbers (K+1)) 0 :=
    hasNaturalDensity_zero_of_summable_reciprocals
      (by simpa only [one_div] using summable_reciprocal_smoothNumbers K)
  have hsmooth' := hsmooth.comp (Nat.tendsto_div_const_atTop ha.ne')
  filter_upwards [hrough, hsmooth.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),
    hsmooth'.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity), eventually_ge_atTop a]
    with N hR hS hS' hNa Y
  by_cases hy : Y ≤ K
  · have hyK : Nat.smoothNumbers (Y+1) ⊆ Nat.smoothNumbers (K+1) :=
      fun n hn ↦ ⟨hn.1, fun p hp ↦ (hn.2 p hp).trans_le (Nat.succ_le_succ hy)⟩
    have hN' := (densityUpTo_mono hyK N).trans_lt hS
    have hM' := (densityUpTo_mono hyK (N/a)).trans_lt hS'
    rw [abs_lt]
    constructor <;> linarith [densityUpTo_nonneg (Nat.smoothNumbers (Y+1)) N,
      densityUpTo_nonneg (Nat.smoothNumbers (Y+1)) (N/a)]
  · have hKY : integerRoughNumbers Y ⊆ integerRoughNumbers K :=
      fun n hn ↦ ⟨hn.1, fun p hp ↦ (Nat.le_of_lt (Nat.lt_of_not_ge hy)).trans_lt (hn.2 p hp)⟩
    have hM : 0 < N/a := (Nat.le_div_iff_mul_le ha).mpr (by simpa using hNa)
    have hMN : N/a ≤ N := Nat.div_le_self _ _
    have hM' : (0 : ℝ) < ((N/a : ℕ) : ℝ) := by exact_mod_cast hM
    have hN : N ≤ (2*a)*(N/a) := by
      have he := Nat.mod_add_div N a
      have hm := (Nat.mod_lt N ha).le
      calc
        N = N%a + a*(N/a) := he.symm
        _ ≤ a + a*(N/a) := Nat.add_le_add_right hm _
        _ ≤ a*(N/a) + a*(N/a) := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hM) _
        _ = _ := by ring
    have hratio : 1 + (N : ℝ)/((N/a : ℕ) : ℝ) ≤ C := by
      have h : (N : ℝ)/((N/a : ℕ) : ℝ) ≤ 2*a :=
        (div_le_iff₀ hM').mpr (by exact_mod_cast hN)
      dsimp [C]
      linarith
    refine (densityUpTo_smooth_dilation_le Y hM hMN).trans_lt ?_
    refine (mul_le_mul (densityUpTo_mono hKY N) hratio (by positivity) (densityUpTo_nonneg _ _)).trans_lt ?_
    exact (lt_div_iff₀ hC).mp hR

end GRHArticle.ProgressionFree
