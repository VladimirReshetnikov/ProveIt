import GowersSzemeredi.Proofs05FourierInterval
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.Lemmas
import GowersSzemeredi.Proofs05Weyl
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs05ModularApproximation
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.NumberTheory.Divisors

/-!
# Lemma 5.5 for polynomial value sequences

The displayed proof of Lemma 5.5 applies a Fourier estimate for a set to a
polynomial value sequence as if that sequence had no collisions.  Below we
instead use the multiplicity function of that sequence; its Fourier transform
is the required Weyl sum even when values collide.  The final route uses the
result in the form `lemma_5_5_square_root_auxiliary_holds`.

There is also a quantitative transcription issue in the induction: the first
two occurrences of the leading-coefficient bound must have exponent
`-1 / (k * 2^(k+1))`, not `-1 / (k * 2^(k+2))`, in order for the displayed
choice of the chunk length `u` to yield the following `k+2` exponent.

The 25 declarations of this module that the final route does not use are in
`Proofs05PolynomialPartitionSide`: among them the printed `lemma_5_5_holds`
and the audit of the former Corollary 5.6.  Its exact-cell, almost-equal
partition is false (`corollary_5_6_exact_partition_counterexample`, with the
identity polynomial modulo two: at the claimed diameter scale every cell must
be parity homogeneous, while the prescribed equal cell size cannot divide the
number of even elements in the interval).  The repaired live target-length
statement is the form actually delivered by the printed induction. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## A collision-safe missing-interval estimate -/

private def weightedCenteredCode {N : Nat} (r : ZMod N) : Nat × Bool :=
  (centeredAbs r, decide (0 ≤ r.valMinAbs))

private lemma weightedCenteredCode_injective {N : Nat} :
    Function.Injective (weightedCenteredCode (N := N)) := by
  intro a b hab
  simp only [weightedCenteredCode, centeredAbs, Prod.mk.injEq, decide_eq_decide] at hab
  exact ZMod.injective_valMinAbs (by omega)

private lemma weighted_centered_reciprocal_sq_tail {N K : Nat} [NeZero N]
    (hK : 0 < K) :
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N => K < centeredAbs r),
      (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) ≤ 2 / K := by
  let H : Finset (ZMod N) :=
    Finset.univ.filter fun r : ZMod N => K < centeredAbs r
  -- `r ↦ (|r|, sign r)` embeds `H` into `(K, max K N] × Bool`
  have himage : H.image weightedCenteredCode ⊆ Finset.Ioc K (max K N) ×ˢ Finset.univ := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_univ, and_true]
    exact ⟨(Finset.mem_filter.mp hr).2,
      (ZMod.natAbs_valMinAbs_le r).trans ((Nat.div_le_self N 2).trans (le_max_right K N))⟩
  calc
    _ = ∑ p ∈ H.image weightedCenteredCode, (((p.1 : Nat) : Real) ^ 2)⁻¹ :=
      (Finset.sum_image weightedCenteredCode_injective.injOn).symm
    _ ≤ ∑ p ∈ Finset.Ioc K (max K N) ×ˢ Finset.univ, (((p.1 : Nat) : Real) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg himage fun _ _ _ => by positivity
    _ = 2 * ∑ n ∈ Finset.Ioc K (max K N), (((n : Nat) : Real) ^ 2)⁻¹ := by
      simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]
    _ ≤ 2 * ((K : Real)⁻¹ - ((max K N : Nat) : Real)⁻¹) := by
      gcongr
      exact sum_Ioc_inv_sq_le_sub hK.ne' (le_max_left K N)
    _ ≤ 2 / K := by
      rw [div_eq_mul_inv]
      gcongr
      exact sub_le_self _ (by positivity)

private lemma fourier_natWeight_norm_le_mass {N : Nat} [NeZero N]
    (w : ZMod N → Nat) (r : ZMod N) :
    ‖fourier (fun x => (w x : Complex)) r‖ ≤ ∑ x, w x := by
  rw [fourier, ZMod.dft_apply, Nat.cast_sum]
  simpa only [smul_eq_mul, norm_mul, AddChar.norm_apply, Complex.norm_natCast, one_mul] using
    norm_sum_le Finset.univ
      (fun x : ZMod N => ZMod.stdAddChar (-(x * r)) • (w x : Complex))

@[simp] private lemma fourier_natWeight_zero {N : Nat} [NeZero N]
    (w : ZMod N → Nat) :
    fourier (fun x => (w x : Complex)) 0 = ((∑ x, w x : Nat) : Complex) := by
  simp [fourier, ZMod.dft_apply]

attribute [simp] fourier_indicator_zero

private lemma weighted_centeredInterval_sub_mem {N L : Nat} [NeZero N]
    {x y : ZMod N} (hx : x ∈ centeredInterval N L)
    (hy : y ∈ centeredInterval N L) :
    x - y ∈ centeredInterval N (L + L) := by
  simp only [centeredInterval, Finset.mem_image] at hx hy ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a - b, ?_, by push_cast; rfl⟩
  simp only [Finset.mem_Ico] at ha hb ⊢
  constructor <;> (push_cast at *; omega)

private lemma weighted_centeredInterval_card (N L : Nat) [NeZero N]
    (hLN : 2 * L ≤ N) :
    (centeredInterval N L).card = 2 * L := by
  rw [centeredInterval, Finset.card_image_iff.mpr]
  · simp only [Int.card_Ico, sub_neg_eq_add]
    rw [Int.toNat_add (by positivity) (by positivity)]
    simp
    omega
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_Ico] at hx hy
    have hdvd : (N : Int) ∣ y - x :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub x y N).mp hxy
    have habs : |y - x| < (N : Int) := by
      have hlower : -(2 * (L : Int)) < y - x := by linarith
      have hupper : y - x < 2 * (L : Int) := by linarith
      have hLN' : (2 * (L : Int)) ≤ N := by exact_mod_cast hLN
      rw [abs_lt]
      exact ⟨lt_of_le_of_lt (neg_le_neg hLN') hlower, hupper.trans_le hLN'⟩
    have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith

private lemma correlation_centeredInterval_eq_zero_of_not_mem {N L : Nat}
    [NeZero N] {a : ZMod N} (ha : a ∉ centeredInterval N (L + L)) :
    correlation (indicator (centeredInterval N L))
      (indicator (centeredInterval N L)) a = 0 := by
  unfold correlation
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ centeredInterval N L
  · have hxa : x - a ∉ centeredInterval N L := by
      intro hmem
      apply ha
      have hsub := weighted_centeredInterval_sub_mem hx hmem
      convert hsub using 1
      abel
    simp [indicator, hx, hxa]
  · simp [indicator, hx]

private lemma weighted_fourier_energy_relation {N L : Nat} [NeZero N]
    (w : ZMod N → Nat)
    (hzero : ∀ a ∈ centeredInterval N (L + L), w a = 0) :
    (∑ r : ZMod N, fourier (fun x => (w x : Complex)) r *
      ((‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 : Real) : Complex)) = 0 := by
  let I : ZMod N → Complex := indicator (centeredInterval N L)
  have hparse := identity_2_2_holds N (fun x => (w x : Complex)) (correlation I I)
  have hright :
      (∑ s : ZMod N, (w s : Complex) * star (correlation I I s)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s ∈ centeredInterval N (L + L)
    · rw [hzero s hs]
      simp
    · rw [correlation_centeredInterval_eq_zero_of_not_mem hs]
      simp
  rw [hright, mul_zero] at hparse
  rw [← hparse]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [identity_2_1_holds N I I r]
  simp only [star_mul, star_star]
  congr 1
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]

/-- Collision-safe form of Lemma 5.2.  A natural-valued weight of total mass
`t` which vanishes on the centered interval has a large low nonzero Fourier
coefficient. -/
theorem weighted_missing_interval_fourier
    (N M t : Nat) [NeZero N] (w : ZMod N → Nat)
    (hN : 1 < N) (hM : 0 < M) (hEven : Even M) (hMN : 2 * M ≤ N)
    (hmass : ∑ x, w x = t)
    (hzero : ∀ x ∈ centeredInterval N M, w x = 0) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤ (N : Real) ^ 2 / (M : Real) ^ 2 ∧
      (t : Real) * M / (4 * N) ≤
        ‖fourier (fun x => (w x : Complex)) r‖ := by
  obtain ⟨L, rfl⟩ := hEven
  have hL : 0 < L := by omega
  have hIL : 2 * L ≤ N := by omega
  have hden : 0 < (L + L) ^ 2 := by positivity
  -- the frequency threshold `K = ⌊N ^ 2 / (L + L) ^ 2⌋`
  obtain ⟨K, hKmul, hfloor⟩ : ∃ K : Nat, K * (L + L) ^ 2 ≤ N ^ 2 ∧
      N ^ 2 < (K + 1) * (L + L) ^ 2 :=
    ⟨_, Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self _)⟩
  have hfour : 4 * (L + L) ^ 2 ≤ N ^ 2 := by linarith [Nat.mul_le_mul hMN hMN]
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by rintro rfl; linarith)
  have hthree : (3 : Real) * N ^ 2 ≤ 4 * K * (L + L : Nat) ^ 2 := by
    exact_mod_cast (by linarith : 3 * N ^ 2 ≤ 4 * K * (L + L) ^ 2)
  have hKratio : (K : Real) ≤ (N : Real) ^ 2 / ((L + L : Nat) : Real) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast hKmul
  have hIcard : (centeredInterval N L).card = L + L := by
    simpa [two_mul] using weighted_centeredInterval_card N L hIL
  -- the zero frequency of the energy identity carries `t (L + L) ^ 2`
  have hlower : (t : Real) * (L + L : Nat) ^ 2 ≤ ∑ r ∈ Finset.univ.erase (0 : ZMod N),
      ‖fourier (fun x => (w x : Complex)) r‖ *
        ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
    have h := weighted_fourier_energy_relation w hzero
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod N)), fourier_natWeight_zero,
      fourier_indicator_zero, hmass, hIcard, add_eq_zero_iff_neg_eq] at h
    have h2 := congrArg norm h
    simp only [norm_neg, norm_mul, Complex.norm_natCast, Complex.norm_real, norm_pow,
      Real.norm_natCast] at h2
    rw [h2]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun r _ => by
      simp only [norm_mul, Complex.norm_real, norm_pow, norm_norm])
  by_contra hnot
  have hlow {r : ZMod N} (hr0 : r ≠ 0) (hrK : centeredAbs r ≤ K) :
      ‖fourier (fun x => (w x : Complex)) r‖ < (t : Real) * (L + L : Nat) / (4 * N) :=
    lt_of_not_ge fun h => hnot ⟨r, hr0, (Nat.cast_le.mpr hrK).trans hKratio, h⟩
  have htpos : (0 : Real) < t := by
    haveI : Fact (1 < N) := ⟨hN⟩
    have h1 := (norm_nonneg _).trans_lt (hlow (r := 1) one_ne_zero
      ((by simpa using lemma55_centeredAbs_intCast_le (N := N) 1 :
        centeredAbs (1 : ZMod N) ≤ 1).trans hKpos))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun ht => by simp [ht] at h1)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (0 : ZMod N))
    (fun r => centeredAbs r ≤ K) fun r => ‖fourier (fun x => (w x : Complex)) r‖ *
      ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2
  -- frequencies up to `K` carry at most a quarter of the energy (Parseval for the interval)
  have hlowSum : ∑ r ∈ (Finset.univ.erase (0 : ZMod N)).filter (fun r => centeredAbs r ≤ K),
      ‖fourier (fun x => (w x : Complex)) r‖ *
        ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 ≤
      (t : Real) * (L + L : Nat) ^ 2 / 4 := by
    calc
      _ ≤ ∑ r, (t : Real) * (L + L : Nat) / (4 * N) *
          ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        refine (Finset.sum_le_sum fun r hr => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun _ _ _ => by positivity)
        simp only [Finset.mem_filter, Finset.mem_erase] at hr
        exact mul_le_mul_of_nonneg_right (hlow hr.1.1 hr.2).le (sq_nonneg _)
      _ = _ := by
        rw [← Finset.mul_sum, lemma78_fourier_indicator_energy, hIcard]
        field_simp [NeZero.ne N]
  -- the higher ones at most two thirds (Lemma 5.1 and the reciprocal-square tail)
  have hhighSum : ∑ r ∈ (Finset.univ.erase (0 : ZMod N)).filter (fun r => ¬centeredAbs r ≤ K),
      ‖fourier (fun x => (w x : Complex)) r‖ *
        ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 ≤
      2 / 3 * t * (L + L : Nat) ^ 2 := by
    calc
      _ ≤ ∑ r ∈ Finset.univ.filter (fun r : ZMod N => K < centeredAbs r),
          (t : Real) * N ^ 2 / 4 * (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by
        refine (Finset.sum_le_sum fun r hr => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ r,
            not_le.mp (Finset.mem_filter.mp hr).2⟩) fun _ _ _ => by positivity)
        have hw : ‖fourier (fun x => (w x : Complex)) r‖ ≤ t := by
          rw [← hmass]
          exact fourier_natWeight_norm_le_mass w r
        have hI := (lemma_5_1_holds N L hIL r).2
          (bne_iff_ne.mpr (Finset.mem_erase.mp (Finset.mem_filter.mp hr).1).1)
        calc _ ≤ (t : Real) * ((N : Real) / (2 * centeredAbs r)) ^ 2 := by gcongr
          _ = _ := by ring
      _ ≤ (t : Real) * N ^ 2 / 4 * (2 / K) := by
        rw [← Finset.mul_sum]
        gcongr
        exact weighted_centered_reciprocal_sq_tail hKpos
      _ ≤ _ := by
        rw [show (t : Real) * N ^ 2 / 4 * (2 / K) = t * N ^ 2 / (2 * K) by ring,
          div_le_iff₀ (by positivity)]
        linarith [mul_le_mul_of_nonneg_left hthree htpos.le]
  have hpos : (0 : Real) < (t : Real) * (L + L : Nat) ^ 2 := by positivity
  linarith

/-! The weight used for polynomial recurrence counts occurrences rather than
discarding repeated values.  This is the precise repair of the collision in
the printed proof of Lemma 5.5. -/

noncomputable def polynomialValueMultiplicity {N : Nat}
    (k t : Nat) (a : ZMod N) (x : ZMod N) : Nat :=
  ((Finset.Icc 1 t).filter fun s : Nat => ((s : ZMod N) ^ k) * a = x).card

lemma polynomialValueMultiplicity_mass {N k t : Nat} [NeZero N]
    (a : ZMod N) :
    ∑ x : ZMod N, polynomialValueMultiplicity k t a x = t := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := Finset.Icc 1 t) (t := (Finset.univ : Finset (ZMod N)))
    (f := fun s : Nat => ((s : ZMod N) ^ k) * a) (by simp)
  simpa [polynomialValueMultiplicity, Nat.card_Icc] using hfiber.symm

lemma centeredAbs_le_of_mem_centeredInterval {N M : Nat} [NeZero N]
    (hMN : 2 * M ≤ N) {x : ZMod N} (hx : x ∈ centeredInterval N M) :
    centeredAbs x ≤ M := by
  simp only [centeredInterval, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  simp only [Finset.mem_Ico] at hz
  by_cases hboundary : z * 2 = -(N : Int)
  · have _ : N ≤ 2 * M := by
      exact_mod_cast (show (N : Int) ≤ 2 * M by linarith)
    have hhalf : N / 2 ≤ M := by omega
    exact (ZMod.natAbs_valMinAbs_le (z : ZMod N)).trans hhalf
  · have hlower : -(N : Int) < z * 2 := by
      have : -(N : Int) ≤ z * 2 := by
        linarith
      exact lt_of_le_of_ne this (Ne.symm hboundary)
    have hupper : z * 2 ≤ (N : Int) := by
      linarith
    have hval : ((z : ZMod N).valMinAbs) = z :=
      (ZMod.valMinAbs_spec (z : ZMod N) z).2
        ⟨rfl, ⟨hlower, hupper⟩⟩
    rw [centeredAbs, hval]
    have hzabs : (z.natAbs : Int) ≤ (M : Int) := by omega
    exact_mod_cast hzabs

lemma polynomialValueMultiplicity_zero_of_avoids {N k t M : Nat}
    [NeZero N] (a : ZMod N)
    (havoid : ∀ s ∈ Finset.Icc 1 t,
      ((s : ZMod N) ^ k) * a ∉ centeredInterval N M) :
    ∀ x ∈ centeredInterval N M, polynomialValueMultiplicity k t a x = 0 := by
  intro x hx
  rw [polynomialValueMultiplicity, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsIcc, hsvalue⟩ := Finset.mem_filter.mp hs
  exact havoid s hsIcc (hsvalue ▸ hx)

private lemma fourier_polynomialValueMultiplicity {N k t : Nat} [NeZero N]
    (a r : ZMod N) :
    fourier (fun x => (polynomialValueMultiplicity k t a x : Complex)) r =
      ∑ s ∈ Finset.Icc 1 t,
        exponential (-((((s : ZMod N) ^ k) * a) * r)) := by
  rw [fourier, ZMod.dft_apply]
  simp only [smul_eq_mul, polynomialValueMultiplicity,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  simp_rw [Finset.mul_sum]
  simpa only [exponential, mul_one] using
    (Finset.sum_fiberwise' (Finset.Icc 1 t)
      (fun s : Nat => ((s : ZMod N) ^ k) * a)
      (fun x : ZMod N => ZMod.stdAddChar (-(x * r))))

private lemma exponential_polynomial_eq_realExponential {N k : Nat} [NeZero N]
    (a r : ZMod N) (s : Nat) :
    exponential (-((((s : ZMod N) ^ k) * a) * r)) =
      realExponential
        (-(a * r).valMinAbs / (N : Real) * (s : Real) ^ k) := by
  unfold exponential
  calc
    ZMod.stdAddChar (-((((s : ZMod N) ^ k) * a) * r)) =
        ZMod.stdAddChar
          (((-((s : Int) ^ k) * (a * r).valMinAbs : Int) : ZMod N)) := by push_cast; ring_nf
    _ = Complex.exp
        (2 * Real.pi * Complex.I *
          (-((s : Int) ^ k) * (a * r).valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe _
    _ = realExponential
        (-(a * r).valMinAbs / (N : Real) * (s : Real) ^ k) := by
      unfold realExponential
      congr 1
      push_cast
      ring

lemma fourier_polynomialValueMultiplicity_eq_weylSum
    {N k t : Nat} [NeZero N] (a r : ZMod N) :
    fourier (fun x => (polynomialValueMultiplicity k t a x : Complex)) r =
      weylSum (-(a * r).valMinAbs / (N : Real)) k t := by
  rw [fourier_polynomialValueMultiplicity]
  unfold weylSum
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [exponential_polynomial_eq_realExponential]

/-- The weighted missing-interval argument with the number of sampled
polynomial values separated from the recurrence scale.  This is the form
needed when the sample length is `floor (sqrt t)` but the desired recurrence
has the stronger scale `t ^ (-gamma) * N`. -/
theorem polynomial_missing_interval_witness_at_scale
    {N k u M : Nat} [NeZero N] (a : ZMod N) (scale : Real)
    (hu : 2 ≤ u) (huN : u ≤ N) (hM : 0 < M) (hMeven : Even M)
    (hMN : 2 * M ≤ N) (hMscale : (M : Real) ≤ scale)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ u →
      scale < (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤ (N : Real) ^ 2 / (M : Real) ^ 2 ∧
      (u : Real) * M / (4 * N) ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k u‖ := by
  have havoid (s : Nat) (hs : s ∈ Finset.Icc 1 u) :
      ((s : ZMod N) ^ k) * a ∉ centeredInterval N M := fun hsc =>
    (hno s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2).not_ge <|
      (Nat.cast_le.mpr (centeredAbs_le_of_mem_centeredInterval hMN hsc)).trans hMscale
  simpa only [fourier_polynomialValueMultiplicity_eq_weylSum] using
    weighted_missing_interval_fourier N M u (polynomialValueMultiplicity k u a) (by omega) hM
      hMeven hMN (polynomialValueMultiplicity_mass a)
      (polynomialValueMultiplicity_zero_of_avoids a havoid)

lemma twice_floor_quarter_bounds {x : Real} (hx : 8 ≤ x) :
    let M := 2 * Nat.floor (x / 4)
    0 < M ∧ Even M ∧ (M : Real) ≤ x / 2 ∧ x / 4 ≤ M := by
  let u : Nat := Nat.floor (x / 4)
  have hx0 : 0 ≤ x / 4 := by positivity
  have huUpper : (u : Real) ≤ x / 4 := Nat.floor_le hx0
  have huLower : x / 4 < (u : Real) + 1 := Nat.lt_floor_add_one (x / 4)
  have huOne : 1 ≤ u := by
    apply Nat.le_floor
    linarith
  dsimp only
  refine ⟨by omega, even_two_mul u, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

lemma weylThreshold_sixtyFour_le {k : Nat} (hk : 2 ≤ k) :
    64 ≤ weylThreshold k := by
  have hkCubePos : 0 < k ^ 3 := by positivity
  have hinnerExponent : 3 ≤ 40 * k ^ 3 := by omega
  have houterExponent : 6 ≤ 2 ^ (40 * k ^ 3) := by
    have hpow : 2 ^ 3 ≤ 2 ^ (40 * k ^ 3) :=
      pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : Nat)) hinnerExponent
    norm_num at hpow ⊢
    omega
  have hpow : 2 ^ 6 ≤ 2 ^ (2 ^ (40 * k ^ 3)) :=
    pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : Nat)) houterExponent
  simpa [weylThreshold] using hpow

private lemma recurrenceExponent_le_half {k : Nat} (hk : 2 ≤ k) :
    (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) ≤ 1 / 2 := by
  have hkReal : (2 : Real) ≤ k := by exact_mod_cast hk
  have hpow : (1 : Real) ≤ (2 : Real) ^ (k + 1) :=
    one_le_pow₀ (by norm_num)
  have hden : (2 : Real) ≤ (k : Real) * (2 : Real) ^ (k + 1) := by
    nlinarith
  have hdenPos : (0 : Real) < (k : Real) * (2 : Real) ^ (k + 1) := by positivity
  simpa only [one_div] using
    (inv_le_inv₀ hdenPos (by norm_num : (0 : Real) < 2)).2 hden

lemma recurrenceScale_eight_le {k t N : Nat}
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ t) (htN : t ≤ N) :
    8 ≤ (t : Real) ^
      (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N := by
  have ht64 : (64 : Real) ≤ t := by exact_mod_cast (weylThreshold_sixtyFour_le hk).trans ht
  have h8 : (8 : Real) ≤ (t : Real) ^ (1 / 2 : Real) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt' (by norm_num : (0 : Real) < 8)]; linarith
  calc (8 : Real) ≤ (t : Real) ^ (1 - ((k : Real) * 2 ^ (k + 1))⁻¹) :=
        h8.trans (Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by linarith [recurrenceExponent_le_half hk]))
    _ = (t : Real) ^ (-((k : Real) * 2 ^ (k + 1))⁻¹) * t := by
        rw [sub_eq_neg_add, Real.rpow_add (by linarith : (0 : Real) < t), Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast htN) (by positivity)

lemma recurrenceScale_le_N {k t N : Nat} (ht : 1 ≤ t) :
    (t : Real) ^
      (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N ≤ N := by
  have htOne : (1 : Real) ≤ t := by exact_mod_cast ht
  have hpow :
      (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos htOne
      (neg_nonpos.mpr (by positivity))
  have hN : (0 : Real) ≤ N := by positivity
  calc
    (t : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N ≤ 1 * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ = N := one_mul _

/-- The large-Weyl-sum witness used for the square-root recurrence.  The
Fourier sum has length `u`, while its avoided interval has the target scale
`t ^ (-gamma) * N`. -/
private theorem polynomial_weyl_sqrt_witness
    {N k t u : Nat} [NeZero N] (a : ZMod N)
    (hk : 2 ≤ k) (hWu : weylThreshold k ≤ u) (hu : 2 ≤ u)
    (huT : u ≤ t) (htN : t ≤ N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ u →
      (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤
        16 * (t : Real) ^
          (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) ∧
      (u : Real) * (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k u‖ := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have hWt : weylThreshold k ≤ t := hWu.trans huT
  have ht64 : 64 ≤ t := (weylThreshold_sixtyFour_le hk).trans hWt
  have htPos : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- the avoided interval has half-length `M = 2 ⌊scale / 4⌋` at `scale = t ^ (-gamma) N`
  have h8 : 8 ≤ (t : Real) ^ (-gamma) * N := recurrenceScale_eight_le hk hWt htN
  have hle : (t : Real) ^ (-gamma) * N ≤ N := recurrenceScale_le_N (by omega)
  obtain ⟨hMpos, hMeven, hMupper, hMlower⟩ := twice_floor_quarter_bounds h8
  set M := 2 * ⌊(t : Real) ^ (-gamma) * N / 4⌋₊
  obtain ⟨r, hr0, hrsize, hrlarge⟩ := polynomial_missing_interval_witness_at_scale a
    ((t : Real) ^ (-gamma) * N) hu (huT.trans htN) hMpos hMeven
    (by exact_mod_cast (by linarith : (2 : Real) * M ≤ N)) (by linarith) hno
  have hNM : (N : Real) ≤ 4 * (t : Real) ^ gamma * M := by
    have h := mul_le_mul_of_nonneg_left hMlower (Real.rpow_nonneg htPos.le gamma)
    rw [← mul_div_assoc, ← mul_assoc, ← Real.rpow_add htPos, add_neg_cancel,
      Real.rpow_zero, one_mul] at h
    linarith
  refine ⟨r, hr0, hrsize.trans ?_, le_trans ?_ hrlarge⟩
  · show _ ≤ 16 * (t : Real) ^ (2 * gamma)
    rw [div_le_iff₀ (by positivity), two_mul, Real.rpow_add htPos]
    linarith [pow_le_pow_left₀ (by positivity) hNM 2]
  · show (u : Real) * (t : Real) ^ (-gamma) / 16 ≤ _
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hMlower (Nat.cast_nonneg (α := Real) u)]

/-! ### Quantitative polynomial recurrence -/

/-- A small, reusable consequence of the repaired double-exponential
threshold.  Keeping `D` and `E` abstract lets the two constant absorptions in
Lemma 5.5 share the same non-evaluating tower argument. -/
lemma lemma55_threshold_root {k t D E : Nat}
    (hD : 0 < D) (hDE : D * E ≤ 2 ^ (40 * k ^ 3))
    (ht : weylThreshold k ≤ t) :
    (2 : Real) ^ E ≤ (t : Real) ^ ((D : Real)⁻¹) := by
  refine (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hD)).mpr ?_
  rw [Real.rpow_natCast, ← pow_mul']
  exact_mod_cast (Nat.pow_le_pow_right two_pos hDE).trans ht

/-- The two constant absorptions needed by the square-root variant. -/
private lemma lemma55_sqrt_threshold_gamma_gap {k u : Nat} (hk : 2 ≤ k)
    (ht : weylThreshold k ≤ u) :
    (192000 : Real) < (u : Real) ^
      (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
  let D := k * 2 ^ (k + 1)
  have hkpow : k ≤ 2 ^ k :=
    (Nat.le_succ k).trans (nat_succ_le_two_pow k)
  have hkCube : k ≤ k ^ 3 := nat_le_cube (by omega)
  have hexponent : 2 * k + 6 ≤ 40 * k ^ 3 := by linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD18 : D * 18 ≤ 2 ^ (40 * k ^ 3) := by
    calc
      D * 18 = k * 2 ^ (k + 1) * 18 := rfl
      _ ≤ 2 ^ k * 2 ^ (k + 1) * 18 :=
        Nat.mul_le_mul_right 18 (Nat.mul_le_mul_right (2 ^ (k + 1)) hkpow)
      _ ≤ 2 ^ k * 2 ^ (k + 1) * 32 := by gcongr; norm_num
      _ = 2 ^ (2 * k + 6) := by ring
      _ ≤ 2 ^ (40 * k ^ 3) :=
        Nat.pow_le_pow_right (by norm_num) hexponent
  have hroot := lemma55_threshold_root hD hD18 ht
  have hDcast : (D : Real) =
      (k : Real) * (2 : Real) ^ (k + 1) := by
    dsimp only [D]
    push_cast
    rfl
  calc
    (192000 : Real) < (2 : Real) ^ 18 := by norm_num
    _ ≤ (u : Real) ^ ((D : Real)⁻¹) := hroot
    _ = (u : Real) ^
        (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by rw [hDcast]

private lemma lemma55_sqrt_threshold_transport_constant {k u : Nat}
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ u) :
    (4 : Real) * 64 ^ (k - 1) ≤
      (u : Real) ^ ((4 * (k : Real))⁻¹) := by
  let D := 4 * k
  let E := 2 + 6 * (k - 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hkSqCube : k ^ 2 ≤ k ^ 3 :=
    pow_le_pow_right₀ (by omega : 1 ≤ k) (by norm_num)
  have hE : E ≤ 6 * k := by omega
  have hpoly : D * E ≤ 40 * k ^ 3 := by
    calc
      D * E ≤ (4 * k) * (6 * k) := by gcongr
      _ = 24 * k ^ 2 := by ring
      _ ≤ 24 * k ^ 3 := Nat.mul_le_mul_left 24 hkSqCube
      _ ≤ 40 * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) (by norm_num)
  have hDE : D * E ≤ 2 ^ (40 * k ^ 3) :=
    hpoly.trans <| (Nat.le_succ (40 * k ^ 3)).trans
      (nat_succ_le_two_pow (40 * k ^ 3))
  have hroot := lemma55_threshold_root hD hDE ht
  have hbase : (4 : Real) * 64 ^ (k - 1) = (2 : Real) ^ E := by
    dsimp only [E]
    calc
      (4 : Real) * 64 ^ (k - 1) =
          (2 : Real) ^ 2 * ((2 : Real) ^ 6) ^ (k - 1) := by norm_num
      _ = (2 : Real) ^ 2 * (2 : Real) ^ (6 * (k - 1)) := by
        rw [pow_mul]
      _ = (2 : Real) ^ (2 + 6 * (k - 1)) := (pow_add _ _ _).symm
  have hDcast : (D : Real) = 4 * (k : Real) := by
    dsimp only [D]
    push_cast
    rfl
  rw [hbase, ← hDcast]
  exact hroot

private lemma lemma55_sqrt_exponent_budget {k : Nat} (hk : 2 ≤ k) :
    (4 * (k : Real))⁻¹ +
        (4 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) +
          (k : Real)⁻¹) * (k - 1) ≤
      1 - 2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by
  have hkReal : (0 : Real) < k := by positivity
  have hpowReal : 4 * (4 * (k : Real) - 2) ≤ 3 * (2 : Real) ^ (k + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have : (j : Real) + 1 ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self (n := j)
    push_cast; rw [pow_succ, pow_succ, pow_succ]; linarith
  have hpowPos : (0 : Real) < (2 : Real) ^ (k + 1) := by positivity
  field_simp [ne_of_gt hkReal, ne_of_gt hpowPos]
  nlinarith

@[simp] lemma lemma55_centeredAbs_neg {N : Nat} [NeZero N]
    (x : ZMod N) : centeredAbs (-x) = centeredAbs x := by
  unfold centeredAbs
  exact ZMod.natAbs_valMinAbs_neg x

lemma lemma55_centeredAbs_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (i : ZMod N) ≤ i := by
  rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (Nat.min_le_left _ _).trans (Nat.mod_le i N)

alias lemma55_natCast_centeredAbs_eq_or_neg := natCast_centeredAbs_eq_or_neg

private lemma lemma55_sqrt_dirichlet_denominator_le {k u q : Nat}
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ u) (hq : 1 ≤ q)
    (hqu : q ≤ u) (alpha : Real)
    (hlower :
      (u : Real) ^
          (1 - 2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 64 ≤
        ‖weylSum alpha k u‖)
    (hupper :
      ‖weylSum alpha k u‖ ≤
        1000 * (u : Real) ^
            (1 + (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) *
          (((q : Real)⁻¹ + (u : Real)⁻¹ +
            (q : Real) * (u : Real) ^ (-(k : Real))) ^
              ((2 : Real) ^ (k - 1))⁻¹)) :
    (q : Real) ≤ (u : Real) ^ ((k : Real)⁻¹) := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have huOne : (1 : Real) ≤ u := by exact_mod_cast hq.trans hqu
  have huPos : (0 : Real) < u := by positivity
  have hk2 : (2 : Real) ≤ k := by exact_mod_cast hk
  have hkInv : (k : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  by_contra hqBound
  -- each term of the Weyl bracket is at most `u ^ (-1 / k)`
  have hB : (q : Real)⁻¹ + (u : Real)⁻¹ + (q : Real) * (u : Real) ^ (-(k : Real)) ≤
      3 * (u : Real) ^ (-(k : Real)⁻¹) := by
    have h1 : (q : Real)⁻¹ ≤ (u : Real) ^ (-(k : Real)⁻¹) := by
      rw [Real.rpow_neg huPos.le]
      exact inv_anti₀ (by positivity) (not_le.mp hqBound).le
    have h2 : (u : Real) ^ (-1 : Real) ≤ (u : Real) ^ (-(k : Real)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_le huOne (by linarith)
    have h3 : (q : Real) * (u : Real) ^ (-(k : Real)) ≤ (u : Real) ^ (-1 : Real) := by
      calc _ ≤ (u : Real) ^ (1 : Real) * (u : Real) ^ (-(k : Real)) := by
            rw [Real.rpow_one]
            gcongr
        _ ≤ _ := by
            rw [← Real.rpow_add huPos]
            exact Real.rpow_le_rpow_of_exponent_le huOne (by linarith)
    rw [Real.rpow_neg_one] at h2 h3
    linarith
  -- so the bracket's root is at most `3 u ^ (-4 gamma)`, as `2 ^ (k + 1) = 4 * 2 ^ (k - 1)`
  have hroot : ((q : Real)⁻¹ + (u : Real)⁻¹ + (q : Real) * (u : Real) ^ (-(k : Real))) ^
      ((2 : Real) ^ (k - 1))⁻¹ ≤ 3 * (u : Real) ^ (-4 * gamma) := by
    have hexp : -(k : Real)⁻¹ * ((2 : Real) ^ (k - 1))⁻¹ = -4 * gamma := by
      show _ = -4 * ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
      rw [show k + 1 = k - 1 + 2 by omega, pow_add]
      ring
    calc _ ≤ (3 * (u : Real) ^ (-(k : Real)⁻¹)) ^ ((2 : Real) ^ (k - 1))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hB (by positivity)
      _ = (3 : Real) ^ ((2 : Real) ^ (k - 1))⁻¹ * (u : Real) ^ (-4 * gamma) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul huPos.le, hexp]
      _ ≤ 3 * (u : Real) ^ (-4 * gamma) := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 3)
            (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num) : (1 : Real) ≤ 2 ^ (k - 1)))
  -- compare with the lower bound: `u ^ gamma ≤ 192000`, against the threshold gap
  have hW : ‖weylSum alpha k u‖ ≤
      1000 * (u : Real) ^ (1 + gamma) * (3 * (u : Real) ^ (-4 * gamma)) :=
    hupper.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  have hlow : (u : Real) ^ (1 - 2 * gamma) / 64 ≤ ‖weylSum alpha k u‖ := hlower
  rw [show (u : Real) ^ (1 - 2 * gamma) =
      (u : Real) ^ (1 + gamma) * (u : Real) ^ (-4 * gamma) * (u : Real) ^ gamma by
    rw [← Real.rpow_add huPos, ← Real.rpow_add huPos]
    congr 1
    ring] at hlow
  have hgap : (192000 : Real) < (u : Real) ^ gamma := lemma55_sqrt_threshold_gamma_gap hk ht
  have hA := Real.rpow_pos_of_pos huPos (1 + gamma)
  have hZ := Real.rpow_pos_of_pos huPos (-4 * gamma)
  linarith [mul_lt_mul_of_pos_left hgap (mul_pos hA hZ)]

private lemma lemma55_sqrt_scale_compare {k t u : Nat} (hk : 2 ≤ k)
    (ht : 1 ≤ t) (hu : 1 ≤ u)
    (htFour : (t : Real) ≤ 4 * (u : Real) ^ 2) :
    (u : Real) ^
          (-2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 4 ≤
      (t : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have huPos : (0 : Real) < u := by exact_mod_cast hu
  have hgamma : gamma ≤ 1 := (recurrenceExponent_le_half hk).trans (by norm_num)
  calc (u : Real) ^ (-2 * gamma) / 4 = (4 : Real) ^ (-1 : Real) * (u : Real) ^ (-2 * gamma) := by
        rw [Real.rpow_neg_one]
        ring
    _ ≤ (4 : Real) ^ (-gamma) * (u : Real) ^ (-2 * gamma) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)
    _ = (4 * (u : Real) ^ 2) ^ (-gamma) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul huPos.le]
        congr 2
        ring
    _ ≤ (t : Real) ^ (-gamma) :=
        Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr ht) htFour
          (neg_nonpos.mpr (by positivity))

private lemma lemma55_sqrt_weyl_lower {k t u : Nat} (hk : 2 ≤ k)
    (ht : 1 ≤ t) (hu : 1 ≤ u)
    (htFour : (t : Real) ≤ 4 * (u : Real) ^ 2) :
    (u : Real) ^
          (1 - 2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 64 ≤
      (u : Real) * (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have huPos : (0 : Real) < u := by exact_mod_cast (show 0 < u by omega)
  have hscale : (u : Real) ^ (-2 * gamma) / 4 ≤ (t : Real) ^ (-gamma) := by
    simpa only [gamma] using lemma55_sqrt_scale_compare hk ht hu htFour
  have hfactor :
      (u : Real) ^ (1 - 2 * gamma) =
        (u : Real) * (u : Real) ^ (-2 * gamma) := by
    calc
      (u : Real) ^ (1 - 2 * gamma) =
          (u : Real) ^ ((1 : Real) + (-2 * gamma)) := by congr 1; ring
      _ = (u : Real) ^ (1 : Real) * (u : Real) ^ (-2 * gamma) := by
        rw [Real.rpow_add huPos]
      _ = (u : Real) * (u : Real) ^ (-2 * gamma) := by rw [Real.rpow_one]
  calc
    (u : Real) ^ (1 - 2 * gamma) / 64 =
        (u : Real) * ((u : Real) ^ (-2 * gamma) / 4) / 16 := by linarith
    _ ≤ (u : Real) * (t : Real) ^ (-gamma) / 16 := by gcongr

/-- The square-root-size strengthening needed by the degree induction.  It
is proved directly at sample length `floor (sqrt t)`, rather than by the
invalid printed inference from the existential conclusion of Lemma 5.5. -/
theorem lemma_5_5_square_root_auxiliary_holds :
    lemma_5_5_square_root_auxiliary := by
  unfold lemma_5_5_square_root_auxiliary
  intro k t N _ hk ht htN a
  let u : Nat := Nat.sqrt t
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have hWu : weylThreshold k ≤ u := (Nat.le_sqrt').2 ht
  have huTwo : 2 ≤ u :=
    (show 2 ≤ 64 by norm_num).trans ((weylThreshold_sixtyFour_le hk).trans hWu)
  have huT : u ≤ t := Nat.sqrt_le_self t
  have huSqT : u ^ 2 ≤ t := Nat.sqrt_le' t
  have htFour : (t : Real) ≤ 4 * (u : Real) ^ 2 := by
    have h : t < (u + 1) ^ 2 := Nat.lt_succ_sqrt' t
    exact_mod_cast (by nlinarith : t ≤ 4 * u ^ 2)
  have huPos : (0 : Real) < u := by exact_mod_cast (show 0 < u by omega)
  have huReal : (1 : Real) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hgamma : gamma ≤ 1 / 2 := recurrenceExponent_le_half hk
  have hwl : (u : Real) ^ (1 - 2 * gamma) / 64 ≤ u * (t : Real) ^ (-gamma) / 16 :=
    lemma55_sqrt_weyl_lower hk (by omega) (by omega) htFour
  by_contra hrecurrence
  -- a frequency `r` with a large Weyl sum, from the missing-interval argument
  obtain ⟨r, hr0, hrsize, hrlarge⟩ := polynomial_weyl_sqrt_witness a hk hWu huTwo huT htN
    fun p hp hpu => lt_of_not_ge fun hpClose =>
      hrecurrence ⟨p, hp, (Nat.pow_le_pow_left hpu 2).trans huSqT, hpClose⟩
  have hs : (centeredAbs r : Real) ≤ 64 * (u : Real) ^ (4 * gamma) := by
    have h4 : (4 : Real) ^ (2 * gamma) ≤ 4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 4)
        (show 2 * gamma ≤ 1 by linarith)
    have hrs : (centeredAbs r : Real) ≤ 16 * (t : Real) ^ (2 * gamma) := hrsize
    calc (centeredAbs r : Real) ≤ 16 * (4 * (u : Real) ^ 2) ^ (2 * gamma) :=
          hrs.trans (by gcongr)
      _ = 16 * ((4 : Real) ^ (2 * gamma) * (u : Real) ^ (4 * gamma)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul huPos.le]
          congr 3
          ring
      _ ≤ 64 * (u : Real) ^ (4 * gamma) := by
          linarith [mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg huPos.le (4 * gamma))]
  -- Dirichlet: `alpha = -(a r) / N` has a denominator `q ≤ u ^ (1 / k)`
  let alpha : Real := -((a * r).valMinAbs : Real) / N
  obtain ⟨b, q, hq, hqu, hbq, happrox⟩ := lemma_5_4_holds alpha u (by omega)
  have hqPos : (0 : Real) < q := by exact_mod_cast hq
  have hqBound : (q : Real) ≤ (u : Real) ^ ((k : Real)⁻¹) := by
    refine lemma55_sqrt_dirichlet_denominator_le hk hWu hq hqu alpha (hwl.trans hrlarge) ?_
    have hgcd : Int.gcd b (q : Int) = 1 := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact hbq.gcd_eq_one
    have happroxSq : |alpha - (b : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹ :=
      happrox.trans (inv_anti₀ (by positivity) (by rw [pow_two]; gcongr))
    simpa using (lemma_5_3_holds k (by omega)).2 u b q alpha hWu
      (by exact_mod_cast (show 0 < q by omega)) hgcd (by simpa using happroxSq)
  -- `p = |r| q` satisfies `4 p ^ (k - 1) ≤ u ^ (1 - 2 gamma)`, hence `p ≤ u`
  obtain ⟨p, hp⟩ : ∃ p : Nat, p = centeredAbs r * q := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hp]
    exact mul_pos (Nat.pos_of_ne_zero fun h =>
      hr0 ((ZMod.valMinAbs_eq_zero r).mp (Int.natAbs_eq_zero.mp h))) (by omega)
  have hpPow : 4 * (p : Real) ^ (k - 1) ≤ (u : Real) ^ (1 - 2 * gamma) := by
    have hpX : (p : Real) ≤ 64 * (u : Real) ^ (4 * gamma + (k : Real)⁻¹) := by
      rw [hp, Nat.cast_mul, Real.rpow_add huPos, ← mul_assoc]
      exact mul_le_mul hs hqBound (by positivity) (by positivity)
    calc 4 * (p : Real) ^ (k - 1) ≤
          4 * (64 * (u : Real) ^ (4 * gamma + (k : Real)⁻¹)) ^ (k - 1) := by gcongr
      _ = 4 * 64 ^ (k - 1) *
          (u : Real) ^ ((4 * gamma + (k : Real)⁻¹) * ((k - 1 : Nat) : Real)) := by
          rw [mul_pow, Real.rpow_mul huPos.le, Real.rpow_natCast]
          ring
      _ ≤ (u : Real) ^ ((4 * (k : Real))⁻¹) *
          (u : Real) ^ ((4 * gamma + (k : Real)⁻¹) * ((k - 1 : Nat) : Real)) := by
          gcongr
          exact lemma55_sqrt_threshold_transport_constant hk hWu
      _ ≤ (u : Real) ^ (1 - 2 * gamma) := by
          rw [← Real.rpow_add huPos, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
          exact Real.rpow_le_rpow_of_exponent_le huReal (lemma55_sqrt_exponent_budget hk)
  have hpu : p ≤ u := by
    have h1 : (p : Real) ≤ (p : Real) ^ (k - 1) :=
      le_self_pow₀ (by exact_mod_cast hp1) (by omega)
    have h2 : (u : Real) ^ (1 - 2 * gamma) ≤ u := by
      simpa using Real.rpow_le_rpow_of_exponent_le huReal (show 1 - 2 * gamma ≤ 1 by
        linarith [show 0 ≤ gamma by positivity])
    exact_mod_cast (by linarith : (p : Real) ≤ u)
  -- reduction modulo `N`: `p ^ k a = ±e₀ p ^ (k - 1)` with `|e₀| ≤ N / u`
  have hmod : (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤
      (N : Real) / u * (p : Real) ^ (k - 1) := by
    subst hp
    exact modular_monomial_of_rational_approximation a r b (by omega) hq huPos happrox
  apply hrecurrence
  refine ⟨p, hp1, (Nat.pow_le_pow_left hpu 2).trans huSqT, hmod.trans ?_⟩
  show _ ≤ (t : Real) ^ (-gamma) * N
  rw [div_mul_eq_mul_div, div_le_iff₀ huPos]
  have hpt : (p : Real) ^ (k - 1) ≤ u * (t : Real) ^ (-gamma) := by linarith
  linarith [mul_le_mul_of_nonneg_left hpt hNPos.le]

end LeanProofs.GowersSzemeredi
