import GowersSzemeredi.Proofs05FourierInterval
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.Lemmas
import GowersSzemeredi.Proofs05Weyl
import GowersSzemeredi.Proofs05_10
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
  have habs : a.valMinAbs.natAbs = b.valMinAbs.natAbs := by
    simpa only [weightedCenteredCode, centeredAbs] using congrArg Prod.fst hab
  have hsign : decide (0 ≤ a.valMinAbs) = decide (0 ≤ b.valMinAbs) := by
    simpa only [weightedCenteredCode] using congrArg Prod.snd hab
  apply ZMod.injective_valMinAbs
  by_cases ha : 0 ≤ a.valMinAbs
  · have hb : 0 ≤ b.valMinAbs := by
      have : decide (0 ≤ b.valMinAbs) = true := by
        rw [← hsign]
        simp [ha]
      simpa using this
    exact (Int.natAbs_inj_of_nonneg_of_nonneg ha hb).mp habs
  · have ha' : a.valMinAbs ≤ 0 := (lt_of_not_ge ha).le
    have hb : b.valMinAbs ≤ 0 := by
      have : decide (0 ≤ b.valMinAbs) = false := by
        rw [← hsign]
        simp [ha]
      have : ¬ 0 ≤ b.valMinAbs := by simpa using this
      exact (lt_of_not_ge this).le
    exact (Int.natAbs_inj_of_nonpos_of_nonpos ha' hb).mp habs

private lemma weighted_centered_reciprocal_sq_tail {N K : Nat} [NeZero N]
    (hK : 0 < K) :
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N => K < centeredAbs r),
      (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) ≤ 2 / K := by
  let H : Finset (ZMod N) :=
    Finset.univ.filter fun r : ZMod N => K < centeredAbs r
  let T : Finset (Nat × Bool) := Finset.Ioc K N ×ˢ Finset.univ
  have habsN (r : ZMod N) : centeredAbs r ≤ N :=
    (ZMod.natAbs_valMinAbs_le r).trans (Nat.div_le_self N 2)
  by_cases hKN : K ≤ N
  · have hcode_mem : ∀ r ∈ H, weightedCenteredCode r ∈ T := by
      intro r hr
      have hrK : K < centeredAbs r := (Finset.mem_filter.mp hr).2
      simp only [T, Finset.mem_product, Finset.mem_Ioc, Finset.mem_univ,
        and_true, weightedCenteredCode]
      exact ⟨hrK, habsN r⟩
    have himage : H.image weightedCenteredCode ⊆ T := by
      intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact hcode_mem r hr
    calc
      (∑ r ∈ (Finset.univ.filter fun r : ZMod N => K < centeredAbs r),
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) =
          ∑ p ∈ H.image weightedCenteredCode,
            (((p.1 : Nat) : Real) ^ 2)⁻¹ := by
            change (∑ r ∈ H, (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) = _
            symm
            rw [Finset.sum_image]
            · rfl
            · exact weightedCenteredCode_injective.injOn
      _ ≤ ∑ p ∈ T, (((p.1 : Nat) : Real) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ = 2 * ∑ n ∈ Finset.Ioc K N, (((n : Nat) : Real) ^ 2)⁻¹ := by
        simp only [T, Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          nsmul_eq_mul, Nat.cast_ofNat]
        rw [Finset.mul_sum]
      _ ≤ 2 * ((K : Real)⁻¹ - (N : Real)⁻¹) := by
        gcongr
        exact sum_Ioc_inv_sq_le_sub (α := Real) hK.ne' hKN
      _ ≤ 2 / K := by
        rw [div_eq_mul_inv]
        gcongr
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  · have hH : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrK : K < centeredAbs r := (Finset.mem_filter.mp hr).2
      have := habsN r
      omega
    simp only [H, hH, Finset.sum_empty]
    positivity

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
  apply Finset.sum_congr rfl
  intro r _
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
  let K : Nat := N ^ 2 / (L + L) ^ 2
  have hden : 0 < (L + L) ^ 2 := by positivity
  have hsquare : (2 * (L + L)) * (2 * (L + L)) ≤ N * N :=
    Nat.mul_le_mul hMN hMN
  have hfour : 4 * (L + L) ^ 2 ≤ N ^ 2 := by linarith
  have hK4 : 4 ≤ K := by
    dsimp only [K]
    exact (Nat.le_div_iff_mul_le hden).2 hfour
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK4
  have hKmul : K * (L + L) ^ 2 ≤ N ^ 2 := by
    dsimp only [K]
    exact Nat.div_mul_le_self _ _
  have hfloor : N ^ 2 < (K + 1) * (L + L) ^ 2 :=
    (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self K)
  have hthree : 3 * N ^ 2 ≤ 4 * K * (L + L) ^ 2 := by linarith
  have hKratio : (K : Real) ≤
      (N : Real) ^ 2 / ((L + L : Nat) : Real) ^ 2 := by
    apply (le_div_iff₀ (show 0 < (((L + L : Nat) : Real) ^ 2) by positivity)).2
    exact_mod_cast hKmul
  let term : ZMod N → Complex := fun r =>
    fourier (fun x => (w x : Complex)) r *
      ((‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 : Real) : Complex)
  have hrelation : ∑ r : ZMod N, term r = 0 := by
    simpa only [term] using weighted_fourier_energy_relation w hzero
  have hIcard : (centeredInterval N L).card = L + L := by
    simpa [two_mul] using weighted_centeredInterval_card N L hIL
  have hterm_zero : term 0 =
      (((t : Real) * (L + L : Nat) ^ 2 : Real) : Complex) := by
    have hnorm : ‖(((L + L : Nat) : Complex))‖ = ((L + L : Nat) : Real) := by
      rw [Complex.norm_natCast]
    simp only [term, fourier_natWeight_zero,
      fourier_indicator_zero, hmass, hIcard]
    rw [hnorm]
    push_cast
    ring
  have hsum_erase :
      ∑ r ∈ (Finset.univ.erase (0 : ZMod N)), term r =
        -(((t : Real) * (L + L : Nat) ^ 2 : Real) : Complex) := by
    have hsplit :
        (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), term r) + term 0 = 0 := by
      rw [Finset.sum_erase_add Finset.univ term
        (Finset.mem_univ (0 : ZMod N))]
      exact hrelation
    rw [hterm_zero] at hsplit
    linear_combination hsplit
  have hlower :
      (t : Real) * (L + L : Nat) ^ 2 ≤
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
          ‖fourier (fun x => (w x : Complex)) r‖ *
            ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
    calc
      (t : Real) * (L + L : Nat) ^ 2 =
          ‖∑ r ∈ (Finset.univ.erase (0 : ZMod N)), term r‖ := by
        rw [hsum_erase, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg]
        positivity
      _ ≤ ∑ r ∈ (Finset.univ.erase (0 : ZMod N)), ‖term r‖ :=
        norm_sum_le _ _
      _ = ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
          ‖fourier (fun x => (w x : Complex)) r‖ *
            ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [term, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
  by_contra hnot
  have hlow_coeff {r : ZMod N} (hr0 : r ≠ 0)
      (hrK : centeredAbs r ≤ K) :
      ‖fourier (fun x => (w x : Complex)) r‖ <
        (t : Real) * (L + L : Nat) / (4 * N) := by
    by_contra hlarge
    apply hnot
    exact ⟨r, hr0, (Nat.cast_le.mpr hrK).trans hKratio, le_of_not_gt hlarge⟩
  by_cases ht : t = 0
  · letI : Fact (1 < N) := ⟨hN⟩
    have hhalf : 1 ≤ N / 2 := by omega
    have habs_one : centeredAbs (1 : ZMod N) = 1 := by
      simp [centeredAbs, ZMod.valMinAbs_def_pos, ZMod.val_one N, hhalf]
    have hbad := hlow_coeff (r := (1 : ZMod N)) one_ne_zero (by rw [habs_one]; omega)
    rw [ht, Nat.cast_zero, zero_mul, zero_div] at hbad
    exact absurd hbad (not_lt.mpr (norm_nonneg _))
  have htpos : (0 : Real) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  let energyTerm : ZMod N → Real := fun r =>
    ‖fourier (fun x => (w x : Complex)) r‖ *
      ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2
  let low : Finset (ZMod N) :=
    (Finset.univ.erase 0).filter fun r => centeredAbs r ≤ K
  -- `r = 0` is not a high frequency: `centeredAbs 0 = 0 ≤ K`
  let high : Finset (ZMod N) := Finset.univ.filter fun r => K < centeredAbs r
  have hsplit :
      (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r) =
        (∑ r ∈ low, energyTerm r) + ∑ r ∈ high, energyTerm r := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase 0) (fun r => centeredAbs r ≤ K)]
    congr 1
    refine Finset.sum_congr (Finset.ext fun r => ?_) fun _ _ => rfl
    simp only [high, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      not_le]
    exact ⟨fun h => h.2, fun hr => ⟨fun hr0 => by subst r; simp [centeredAbs] at hr, hr⟩⟩
  have hthreshold_nonneg :
      0 ≤ (t : Real) * (L + L : Nat) / (4 * N) := by positivity
  have hlow_energy :
      (∑ r ∈ low, energyTerm r) ≤
        (t : Real) * (L + L : Nat) ^ 2 / 4 := by
    calc
      (∑ r ∈ low, energyTerm r) ≤
          ∑ r ∈ low,
            ((t : Real) * (L + L : Nat) / (4 * N)) *
              ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hrbase, hrK⟩ := Finset.mem_filter.mp hr
        have hr0 : r ≠ 0 := (Finset.mem_erase.mp hrbase).1
        have hcoeff := hlow_coeff hr0 hrK
        exact mul_le_mul_of_nonneg_right hcoeff.le (sq_nonneg _)
      _ = ((t : Real) * (L + L : Nat) / (4 * N)) *
          ∑ r ∈ low,
            ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ((t : Real) * (L + L : Nat) / (4 * N)) *
          ∑ r : ZMod N,
            ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hthreshold_nonneg
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun _ _ _ => sq_nonneg _)
      _ = (t : Real) * (L + L : Nat) ^ 2 / 4 := by
        rw [lemma78_fourier_indicator_energy, hIcard]
        field_simp [NeZero.ne N]
  have hhigh_point {r : ZMod N} (hr : r ∈ high) :
      energyTerm r ≤
        ((t : Real) * (N : Real) ^ 2 / 4) *
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by
    have hrK : K < centeredAbs r := (Finset.mem_filter.mp hr).2
    have hr0 : r ≠ 0 := fun hrzero => by subst r; simp [centeredAbs] at hrK
    have habs : (0 : Real) < centeredAbs r := by
      exact_mod_cast hKpos.trans hrK
    have hw : ‖fourier (fun x => (w x : Complex)) r‖ ≤ (t : Real) := by
      rw [← hmass]
      exact fourier_natWeight_norm_le_mass w r
    have hI := (lemma_5_1_holds N L hIL r).2 (bne_iff_ne.mpr hr0)
    dsimp only [energyTerm]
    calc
      ‖fourier (fun x => (w x : Complex)) r‖ *
          ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 ≤
          (t : Real) * ((N : Real) / (2 * centeredAbs r)) ^ 2 := by
        gcongr
      _ = ((t : Real) * (N : Real) ^ 2 / 4) *
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by ring
  have hscaled_tail :
      (N : Real) ^ 2 / (2 * K) ≤
        (2 / 3 : Real) * (L + L : Nat) ^ 2 := by
    have hthreeReal :
        (3 : Real) * (N : Real) ^ 2 ≤
          4 * (K : Real) * (L + L : Nat) ^ 2 := by
      exact_mod_cast hthree
    apply (div_le_iff₀ (show (0 : Real) < 2 * K by positivity)).2
    nlinarith
  have hhigh_energy :
      (∑ r ∈ high, energyTerm r) ≤
        (2 / 3 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by
    calc
      (∑ r ∈ high, energyTerm r) ≤
          ∑ r ∈ high,
            (((t : Real) * (N : Real) ^ 2 / 4) *
              (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) := by
        exact Finset.sum_le_sum fun r hr => hhigh_point hr
      _ = ((t : Real) * (N : Real) ^ 2 / 4) *
          ∑ r ∈ high, (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
      _ ≤ ((t : Real) * (N : Real) ^ 2 / 4) * (2 / K) := by
        exact mul_le_mul_of_nonneg_left (weighted_centered_reciprocal_sq_tail hKpos) (by positivity)
      _ = (t : Real) * ((N : Real) ^ 2 / (2 * K)) := by ring
      _ ≤ (t : Real) * ((2 / 3 : Real) * (L + L : Nat) ^ 2) :=
        mul_le_mul_of_nonneg_left hscaled_tail htpos.le
      _ = (2 / 3 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by ring
  have hupper :
      (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r) ≤
        (11 / 12 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by linarith
  have hmasspos : (0 : Real) < (t : Real) * (L + L : Nat) ^ 2 := by positivity
  nlinarith [hlower.trans hupper]

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
          (((-((s : Int) ^ k) * (a * r).valMinAbs : Int) : ZMod N)) := by push_cast; ring
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
  apply Finset.sum_congr rfl
  intro s _
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
  have hN : 1 < N := lt_of_lt_of_le (by omega : 1 < u) huN
  let w : ZMod N → Nat := polynomialValueMultiplicity k u a
  have hmass : ∑ x : ZMod N, w x = u :=
    polynomialValueMultiplicity_mass a
  have havoid : ∀ s ∈ Finset.Icc 1 u,
      ((s : ZMod N) ^ k) * a ∉ centeredInterval N M := by
    intro s hs hscentered
    have hsBounds := Finset.mem_Icc.mp hs
    have habsNat := centeredAbs_le_of_mem_centeredInterval hMN hscentered
    have habsReal :
        (centeredAbs (((s : ZMod N) ^ k) * a) : Real) ≤ M := by
      exact_mod_cast habsNat
    exact (not_lt_of_ge (habsReal.trans hMscale))
      (hno s hsBounds.1 hsBounds.2)
  have hzero : ∀ x ∈ centeredInterval N M, w x = 0 :=
    polynomialValueMultiplicity_zero_of_avoids a havoid
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    weighted_missing_interval_fourier N M u w hN hM hMeven hMN hmass hzero
  refine ⟨r, hr0, hrsize, ?_⟩
  rwa [fourier_polynomialValueMultiplicity_eq_weylSum] at hrlarge

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
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have ht64Nat : 64 ≤ t := (weylThreshold_sixtyFour_le hk).trans ht
  have ht64 : (64 : Real) ≤ t := by exact_mod_cast ht64Nat
  have htOne : (1 : Real) ≤ t := by linarith
  have htPos : (0 : Real) < t := by linarith
  have hgamma : gamma ≤ 1 / 2 := recurrenceExponent_le_half hk
  have hexponent : (1 / 2 : Real) ≤ 1 - gamma := by linarith
  have hsqrt : (8 : Real) ≤ (t : Real) ^ (1 / 2 : Real) := by
    calc
      (8 : Real) = Real.sqrt 64 := by
        rw [show (64 : Real) = (8 : Real) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (t : Real) := Real.sqrt_le_sqrt ht64
      _ = (t : Real) ^ (1 / 2 : Real) := Real.sqrt_eq_rpow (t : Real)
  have hpow : (t : Real) ^ (1 / 2 : Real) ≤ (t : Real) ^ (1 - gamma) :=
    Real.rpow_le_rpow_of_exponent_le htOne hexponent
  have hcombine :
      (t : Real) ^ (1 - gamma) = (t : Real) ^ (-gamma) * t := by
    rw [show 1 - gamma = -gamma + 1 by ring,
      Real.rpow_add htPos, Real.rpow_one]
  have htNReal : (t : Real) ≤ N := by exact_mod_cast htN
  calc
    (8 : Real) ≤ (t : Real) ^ (1 / 2 : Real) := hsqrt
    _ ≤ (t : Real) ^ (1 - gamma) := hpow
    _ = (t : Real) ^ (-gamma) * t := hcombine
    _ ≤ (t : Real) ^ (-gamma) * N := by
      gcongr

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
  let scale : Real := (t : Real) ^ (-gamma) * N
  let M : Nat := 2 * Nat.floor (scale / 4)
  have hWt : weylThreshold k ≤ t := hWu.trans huT
  have huN : u ≤ N := huT.trans htN
  have hscaleEight : 8 ≤ scale := by
    simpa only [scale, gamma] using recurrenceScale_eight_le hk hWt htN
  obtain ⟨hMpos, hMeven, hMupper, hMlower⟩ :=
    twice_floor_quarter_bounds hscaleEight
  have hscaleN : scale ≤ N := by
    simpa only [scale, gamma] using recurrenceScale_le_N (k := k) (N := N)
      (show 1 ≤ t by omega)
  have hMNReal : (2 : Real) * M ≤ N := by linarith
  have hMN : 2 * M ≤ N := by exact_mod_cast hMNReal
  have hMscale : (M : Real) ≤ scale :=
    hMupper.trans (by linarith [hscaleEight])
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    polynomial_missing_interval_witness_at_scale a scale hu huN hMpos hMeven hMN
      hMscale (by simpa only [scale, gamma] using hno)
  have htOne : 1 ≤ t :=
    (show 1 ≤ 64 by norm_num).trans ((weylThreshold_sixtyFour_le hk).trans hWt)
  have htPos : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMPosReal : (0 : Real) < M := by exact_mod_cast hMpos
  have hpowersCancel : (t : Real) ^ gamma * (t : Real) ^ (-gamma) = 1 := by
    rw [← Real.rpow_add htPos]
    simp
  have hNM : (N : Real) ≤ 4 * (t : Real) ^ gamma * M := by
    refine Eq.trans_le ?_
      (mul_le_mul_of_nonneg_left hMlower (by positivity : (0 : Real) ≤ 4 * (t : Real) ^ gamma))
    calc
      (N : Real) = ((t : Real) ^ gamma * (t : Real) ^ (-gamma)) * N := by
        rw [hpowersCancel, one_mul]
      _ = _ := by dsimp only [scale]; ring
  have hratio :
      (N : Real) ^ 2 / (M : Real) ^ 2 ≤
        16 * (t : Real) ^ (2 * gamma) := by
    rw [div_le_iff₀ (by positivity), show 2 * gamma = gamma + gamma by ring,
      Real.rpow_add htPos]
    nlinarith [pow_le_pow_left₀ (by positivity) hNM 2]
  have hlower :
      (u : Real) * (t : Real) ^ (-gamma) / 16 ≤
        (u : Real) * M / (4 * N) := by
    calc
      (u : Real) * (t : Real) ^ (-gamma) / 16 =
          ((u : Real) / (4 * N)) * (scale / 4) := by
        dsimp only [scale]
        field_simp [ne_of_gt hNPos]
        ring
      _ ≤ ((u : Real) / (4 * N)) * M := by gcongr
      _ = (u : Real) * M / (4 * N) := by ring
  exact ⟨r, hr0, hrsize.trans (by simpa only [gamma] using hratio),
    le_trans (by simpa only [gamma] using hlower) hrlarge⟩

/-! ### Quantitative polynomial recurrence -/

/-- A small, reusable consequence of the repaired double-exponential
threshold.  Keeping `D` and `E` abstract lets the two constant absorptions in
Lemma 5.5 share the same non-evaluating tower argument. -/
lemma lemma55_threshold_root {k t D E : Nat}
    (hD : 0 < D) (hDE : D * E ≤ 2 ^ (40 * k ^ 3))
    (ht : weylThreshold k ≤ t) :
    (2 : Real) ^ E ≤ (t : Real) ^ ((D : Real)⁻¹) := by
  let H := 2 ^ (40 * k ^ 3)
  have hDReal : (0 : Real) < D := by exact_mod_cast hD
  have hbase : ((2 ^ H : Nat) : Real) ≤ t := by
    dsimp only [H]
    exact_mod_cast (show 2 ^ (2 ^ (40 * k ^ 3)) ≤ t by
      simpa only [weylThreshold] using ht)
  calc
    (2 : Real) ^ E ≤
        ((2 : Real) ^ H) ^ ((D : Real)⁻¹) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_natCast_mul (by norm_num : (0 : Real) ≤ 2)]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [mul_comm (H : Real) ((D : Real)⁻¹), le_inv_mul_iff₀ hDReal]
      exact_mod_cast hDE
    _ ≤ (t : Real) ^ ((D : Real)⁻¹) := by
      apply Real.rpow_le_rpow (by positivity)
      · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbase
      · positivity

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
      _ ≤ 2 ^ k * 2 ^ (k + 1) * 32 := by gcongr <;> norm_num
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
  have hpowNat : 4 * (4 * k - 2) ≤ 3 * 2 ^ (k + 1) := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
        calc
          4 * (4 * (k + 1) - 2) ≤ 2 * (4 * (4 * k - 2)) := by omega
          _ ≤ 2 * (3 * 2 ^ (k + 1)) :=
            Nat.mul_le_mul_left 2 (ih (by positivity))
          _ = 3 * 2 ^ ((k + 1) + 1) := by rw [pow_succ]; ring
  have hpowReal :
      4 * (4 * (k : Real) - 2) ≤ 3 * (2 : Real) ^ (k + 1) := by
    have hsubCast : ((4 * k - 2 : Nat) : Real) = 4 * (k : Real) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 4 * k)]
      push_cast
      ring
    rw [← hsubCast]
    exact_mod_cast hpowNat
  have hpowPos : (0 : Real) < (2 : Real) ^ (k + 1) := by positivity
  field_simp [ne_of_gt hkReal, ne_of_gt hpowPos]
  nlinarith

private lemma lemma55_sqrt_p_exponent_budget {k : Nat} (hk : 2 ≤ k) :
    (4 * (k : Real))⁻¹ +
        4 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) +
          (k : Real)⁻¹ ≤ 1 := by
  have hkReal : (0 : Real) < k := by positivity
  have hpow : (8 : Real) ≤ (2 : Real) ^ (k + 1) := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : Nat))
      (by omega : 3 ≤ k + 1))
  have hpowPos : (0 : Real) < (2 : Real) ^ (k + 1) := by positivity
  have hkTwo : (2 : Real) ≤ k := by exact_mod_cast hk
  have htwice :
      2 * (2 : Real) ^ (k + 1) ≤ (k : Real) * (2 : Real) ^ (k + 1) :=
    mul_le_mul_of_nonneg_right hkTwo hpowPos.le
  field_simp [ne_of_gt hkReal, ne_of_gt hpowPos]
  nlinarith [hpow, htwice]

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
  let K : Real := (2 : Real) ^ (k - 1)
  let X : Real := (u : Real) ^ (-(k : Real)⁻¹)
  let B : Real := (q : Real)⁻¹ + (u : Real)⁻¹ +
    (q : Real) * (u : Real) ^ (-(k : Real))
  have huOneNat : 1 ≤ u := hq.trans hqu
  have huOne : (1 : Real) ≤ u := by exact_mod_cast huOneNat
  have huPos : (0 : Real) < u := by positivity
  have hqPos : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have hkReal : (0 : Real) < k := by positivity
  have hKOne : (1 : Real) ≤ K := one_le_pow₀ (by norm_num)
  have hKPos : (0 : Real) < K := lt_of_lt_of_le zero_lt_one hKOne
  have hBNonneg : 0 ≤ B := by positivity
  by_contra hqBound
  have hqLarge : (u : Real) ^ ((k : Real)⁻¹) < q :=
    lt_of_not_ge hqBound
  have hqInv : (q : Real)⁻¹ ≤ X := by
    dsimp only [X]
    rw [Real.rpow_neg huPos.le]
    exact (inv_le_inv₀ hqPos (by positivity)).2 hqLarge.le
  have hkInvLeOne : (k : Real)⁻¹ ≤ 1 :=
    (inv_le_one₀ hkReal).2 (by exact_mod_cast (show 1 ≤ k by omega))
  have huInv : (u : Real)⁻¹ ≤ X := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le huOne (by linarith)
  have hexponent : (1 : Real) - k ≤ -(k : Real)⁻¹ := by
    rw [show -(k : Real)⁻¹ = (-1 : Real) / (k : Real) by
      simp [div_eq_mul_inv]]
    apply (le_div_iff₀ hkReal).2
    have hkTwo : (2 : Real) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg ((k : Real) - 1)]
  have hqTerm :
      (q : Real) * (u : Real) ^ (-(k : Real)) ≤ X := by
    calc
      (q : Real) * (u : Real) ^ (-(k : Real)) ≤
          (u : Real) * (u : Real) ^ (-(k : Real)) := by gcongr
      _ = (u : Real) ^ (1 - (k : Real)) := by
        rw [sub_eq_add_neg, Real.rpow_add huPos, Real.rpow_one]
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le huOne hexponent
  have hB : B ≤ 3 * X := by linarith
  have hKInvLeOne : K⁻¹ ≤ 1 := (inv_le_one₀ hKPos).2 hKOne
  have hthree : (3 : Real) ^ K⁻¹ ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 3) hKInvLeOne
  have hBroot :
      B ^ K⁻¹ ≤ 3 *
        (u : Real) ^ ((-(k : Real)⁻¹) * K⁻¹) := by
    calc
      B ^ K⁻¹ ≤ (3 * X) ^ K⁻¹ :=
        Real.rpow_le_rpow hBNonneg hB (by positivity)
      _ = (3 : Real) ^ K⁻¹ * X ^ K⁻¹ := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ 3 * X ^ K⁻¹ := by gcongr
      _ = 3 * (u : Real) ^ ((-(k : Real)⁻¹) * K⁻¹) := by
        dsimp only [X]
        rw [← Real.rpow_mul huPos.le]
  have hpow : (2 : Real) ^ (k + 1) = 4 * K := by
    dsimp only [K]
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
    ring
  have hrootExponent :
      (-(k : Real)⁻¹) * K⁻¹ = -4 * gamma := by
    dsimp only [gamma]
    rw [hpow]
    field_simp [ne_of_gt hkReal, ne_of_gt hKPos]
  have hupper' :
      ‖weylSum alpha k u‖ ≤
        3000 * (u : Real) ^ (1 - 3 * gamma) := by
    calc
      ‖weylSum alpha k u‖ ≤
          1000 * (u : Real) ^ (1 + gamma) * B ^ K⁻¹ := by
        simpa only [gamma, K, B] using hupper
      _ ≤ 1000 * (u : Real) ^ (1 + gamma) *
          (3 * (u : Real) ^ ((-(k : Real)⁻¹) * K⁻¹)) := by gcongr
      _ = 3000 * (u : Real) ^ (1 - 3 * gamma) := by
        rw [hrootExponent, show (1 : Real) - 3 * gamma = 1 + gamma + -4 * gamma by ring,
          Real.rpow_add huPos (1 + gamma) (-4 * gamma)]
        ring
  have hcombined :
      (u : Real) ^ (1 - 2 * gamma) / 64 ≤
        3000 * (u : Real) ^ (1 - 3 * gamma) :=
    (show (u : Real) ^ (1 - 2 * gamma) / 64 ≤ ‖weylSum alpha k u‖ by
      simpa only [gamma] using hlower).trans hupper'
  have hfactor :
      (u : Real) ^ (1 - 2 * gamma) =
        (u : Real) ^ (1 - 3 * gamma) * (u : Real) ^ gamma := by
    rw [← Real.rpow_add huPos]
    congr 1
    ring
  have hgapUpper : (u : Real) ^ gamma ≤ 192000 :=
    le_of_mul_le_mul_left (show (u : Real) ^ (1 - 3 * gamma) * (u : Real) ^ gamma ≤
        (u : Real) ^ (1 - 3 * gamma) * 192000 by linarith)
      (Real.rpow_pos_of_pos huPos (1 - 3 * gamma))
  have hgapLower : (192000 : Real) < (u : Real) ^ gamma := by
    simpa only [gamma] using lemma55_sqrt_threshold_gamma_gap hk ht
  exact (not_le_of_gt hgapLower) hgapUpper

private lemma lemma55_sqrt_scale_compare {k t u : Nat} (hk : 2 ≤ k)
    (ht : 1 ≤ t) (hu : 1 ≤ u)
    (htFour : (t : Real) ≤ 4 * (u : Real) ^ 2) :
    (u : Real) ^
          (-2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 4 ≤
      (t : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  have huPos : (0 : Real) < u := by exact_mod_cast (show 0 < u by omega)
  have htPos : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hgammaNonneg : 0 ≤ gamma := by dsimp only [gamma]; positivity
  have hgammaOne : gamma ≤ 1 :=
    (recurrenceExponent_le_half hk).trans (by norm_num)
  have hfourExponent : (-1 : Real) ≤ -gamma := by linarith
  have hfourPower : (4 : Real)⁻¹ ≤ (4 : Real) ^ (-gamma) := by
    calc
      (4 : Real)⁻¹ = (4 : Real) ^ (-1 : Real) :=
        (Real.rpow_neg_one _).symm
      _ ≤ (4 : Real) ^ (-gamma) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hfourExponent
  have hfactor :
      (4 * (u : Real) ^ 2) ^ (-gamma) =
        (4 : Real) ^ (-gamma) * (u : Real) ^ (-2 * gamma) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg (u : Real))]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul huPos.le]
    congr 1
    ring
  have htoFour :
      (4 * (u : Real) ^ 2) ^ (-gamma) ≤ (t : Real) ^ (-gamma) :=
    Real.rpow_le_rpow_of_nonpos htPos htFour (neg_nonpos.mpr hgammaNonneg)
  have hfromQuarter :
      (u : Real) ^ (-2 * gamma) / 4 ≤
        (4 * (u : Real) ^ 2) ^ (-gamma) := by
    calc
      (u : Real) ^ (-2 * gamma) / 4 =
          (4 : Real)⁻¹ * (u : Real) ^ (-2 * gamma) := by ring
      _ ≤ (4 : Real) ^ (-gamma) * (u : Real) ^ (-2 * gamma) :=
        mul_le_mul_of_nonneg_right hfourPower (by positivity)
      _ = (4 * (u : Real) ^ 2) ^ (-gamma) := hfactor.symm
  simpa only [gamma] using hfromQuarter.trans htoFour

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
          (u : Real) ^ ((1 : Real) + (-2 * gamma)) := by congr 1 <;> ring
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
  have huOne : 1 ≤ u := by omega
  have huT : u ≤ t := Nat.sqrt_le_self t
  have htOne : 1 ≤ t := huOne.trans huT
  have huSqT : u ^ 2 ≤ t := by
    simpa only [u] using Nat.sqrt_le' t
  have htFour : (t : Real) ≤ 4 * (u : Real) ^ 2 := by
    have h : t < (u + 1) ^ 2 := by
      simpa only [u, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t
    have : t ≤ 4 * u ^ 2 := by nlinarith
    exact_mod_cast this
  by_contra hrecurrence
  have hno : ∀ p : Nat, 1 ≤ p → p ≤ u →
      (t : Real) ^ (-gamma) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real) := fun p hp hpu =>
    lt_of_not_ge fun hpClose => hrecurrence
      ⟨p, hp, (Nat.pow_le_pow_left hpu 2).trans huSqT, by simpa only [gamma] using hpClose⟩
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    polynomial_weyl_sqrt_witness a hk hWu huTwo huT htN (by
      simpa only [gamma] using hno)
  have huPos : (0 : Real) < u := by exact_mod_cast (show 0 < u by omega)
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hgammaHalf : gamma ≤ 1 / 2 := by
    simpa only [gamma] using recurrenceExponent_le_half hk
  have htwoGamma : 2 * gamma ≤ 1 := by linarith
  have hfourPow : (4 : Real) ^ (2 * gamma) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 4) htwoGamma
  have hpowFactor :
      (4 * (u : Real) ^ 2) ^ (2 * gamma) =
        (4 : Real) ^ (2 * gamma) * (u : Real) ^ (4 * gamma) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg (u : Real))]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul huPos.le]
    congr 1
    ring
  have hrsizeU :
      (centeredAbs r : Real) ≤ 64 * (u : Real) ^ (4 * gamma) := by
    calc
      (centeredAbs r : Real) ≤ 16 * (t : Real) ^ (2 * gamma) := by
        simpa only [gamma] using hrsize
      _ ≤ 16 * (4 * (u : Real) ^ 2) ^ (2 * gamma) := by gcongr
      _ = 16 * ((4 : Real) ^ (2 * gamma) *
          (u : Real) ^ (4 * gamma)) := by rw [hpowFactor]
      _ ≤ 16 * (4 * (u : Real) ^ (4 * gamma)) := by gcongr
      _ = 64 * (u : Real) ^ (4 * gamma) := by ring
  have hrlargeU :
      (u : Real) ^ (1 - 2 * gamma) / 64 ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k u‖ :=
    (show (u : Real) ^ (1 - 2 * gamma) / 64 ≤ (u : Real) * (t : Real) ^ (-gamma) / 16 by
      simpa only [gamma] using lemma55_sqrt_weyl_lower hk htOne huOne htFour).trans
      (by simpa only [gamma] using hrlarge)
  let c : Int := (a * r).valMinAbs
  let alpha : Real := -(c : Real) / (N : Real)
  obtain ⟨b, q, hq, hqu, hbq, happrox⟩ :=
    lemma_5_4_holds alpha u huOne
  have hqPos : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have hqInt : (0 : Int) < q := by exact_mod_cast (show 0 < q by omega)
  have hgcd : Int.gcd b (q : Int) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hbq.gcd_eq_one
  have happroxSq :
      |alpha - (b : Real) / (q : Real)| ≤ ((q : Real) ^ 2)⁻¹ := by
    refine happrox.trans (inv_anti₀ (by positivity) ?_)
    rw [pow_two]
    gcongr
  have hweyl :=
    (lemma_5_3_holds k (by omega)).2 u b (q : Int) alpha hWu hqInt hgcd
      (by simpa using happroxSq)
  have hqBound : (q : Real) ≤ (u : Real) ^ ((k : Real)⁻¹) := by
    apply lemma55_sqrt_dirichlet_denominator_le hk hWu hq hqu alpha
    · simpa only [alpha, c] using hrlargeU
    · simpa using hweyl
  let s : Nat := centeredAbs r
  let p : Nat := s * q
  have hsPos : 0 < s := Nat.pos_of_ne_zero fun hsZero =>
    hr0 ((ZMod.valMinAbs_eq_zero r).mp
      (Int.natAbs_eq_zero.mp (by simpa only [s, centeredAbs] using hsZero)))
  have hpOne : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hsPos.ne' (by omega))
  have hsBound : (s : Real) ≤ 64 * (u : Real) ^ (4 * gamma) := by
    simpa only [s] using hrsizeU
  have hpBound :
      (p : Real) ≤
        64 * (u : Real) ^ (4 * gamma + (k : Real)⁻¹) := by
    calc
      (p : Real) = (s : Real) * q := by dsimp only [p]; push_cast; rfl
      _ ≤ (64 * (u : Real) ^ (4 * gamma)) *
          (u : Real) ^ ((k : Real)⁻¹) :=
        mul_le_mul hsBound hqBound (by positivity) (by positivity)
      _ = 64 * (u : Real) ^ (4 * gamma + (k : Real)⁻¹) := by
        rw [Real.rpow_add huPos]
        ring
  have hconst :
      (4 : Real) * 64 ^ (k - 1) ≤
        (u : Real) ^ ((4 * (k : Real))⁻¹) :=
    lemma55_sqrt_threshold_transport_constant hk hWu
  have h64Pow : (64 : Real) ≤ 64 ^ (k - 1) := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 64)
        (by omega : 1 ≤ k - 1)
  have h64 : (64 : Real) ≤ (u : Real) ^ ((4 * (k : Real))⁻¹) := by linarith
  have hpBudget :
      (4 * (k : Real))⁻¹ + 4 * gamma + (k : Real)⁻¹ ≤ 1 := by
    simpa only [gamma] using lemma55_sqrt_p_exponent_budget hk
  have huReal : (1 : Real) ≤ u := by exact_mod_cast huOne
  have hpLeUReal : (p : Real) ≤ u := by
    calc
      (p : Real) ≤ (u : Real) ^ ((4 * (k : Real))⁻¹) *
          (u : Real) ^ (4 * gamma + (k : Real)⁻¹) := hpBound.trans (by gcongr)
      _ = (u : Real) ^ ((4 * (k : Real))⁻¹ + (4 * gamma + (k : Real)⁻¹)) :=
        (Real.rpow_add huPos _ _).symm
      _ ≤ (u : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le huReal (by linarith)
      _ = u := Real.rpow_one _
  have hpLeU : p ≤ u := by exact_mod_cast hpLeUReal
  have hpSqT : p ^ 2 ≤ t :=
    (Nat.pow_le_pow_left hpLeU 2).trans huSqT
  have hbudget :
      (4 * (k : Real))⁻¹ +
          (4 * gamma + (k : Real)⁻¹) * (k - 1) ≤ 1 - 2 * gamma := by
    simpa only [gamma] using lemma55_sqrt_exponent_budget hk
  have hkSubCast : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hUpow :
      (((u : Real) ^ (4 * gamma + (k : Real)⁻¹)) ^ (k - 1)) =
        (u : Real) ^
          ((4 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul huPos.le, hkSubCast]
  have hpPowFour :
      4 * (p : Real) ^ (k - 1) ≤ (u : Real) ^ (1 - 2 * gamma) := by
    calc
      4 * (p : Real) ^ (k - 1) ≤
          4 * (64 * (u : Real) ^ (4 * gamma + (k : Real)⁻¹)) ^ (k - 1) := by
        gcongr
      _ = (4 * (64 : Real) ^ (k - 1)) *
          (u : Real) ^ ((4 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
        rw [mul_pow, hUpow]
        ring
      _ ≤ (u : Real) ^ ((4 * (k : Real))⁻¹) *
          (u : Real) ^ ((4 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) := by
        gcongr
      _ = (u : Real) ^
          ((4 * (k : Real))⁻¹ + (4 * gamma + (k : Real)⁻¹) * ((k : Real) - 1)) :=
        (Real.rpow_add huPos _ _).symm
      _ ≤ (u : Real) ^ (1 - 2 * gamma) :=
        Real.rpow_le_rpow_of_exponent_le huReal (by simpa only [hkSubCast] using hbudget)
  have hpPow :
      (p : Real) ^ (k - 1) ≤ (u : Real) ^ (1 - 2 * gamma) / 4 := by linarith
  let e₀ : Int := -c * (q : Int) - b * (N : Int)
  let E : Int := e₀ * (p : Int) ^ (k - 1)
  have hfraction :
      alpha - (b : Real) / (q : Real) =
        (e₀ : Real) / ((N : Real) * (q : Real)) := by
    dsimp only [alpha, e₀]
    push_cast
    field_simp [ne_of_gt hNPos, ne_of_gt hqPos]
  have happrox' :
      |(e₀ : Real)| / ((N : Real) * (q : Real)) ≤
        ((q : Real) * u)⁻¹ := by
    rw [← abs_of_pos (mul_pos hNPos hqPos), ← abs_div, ← hfraction]
    exact happrox
  have he₀Bound : |(e₀ : Real)| ≤ (N : Real) / u := by
    calc
      |(e₀ : Real)| ≤
          ((q : Real) * u)⁻¹ * ((N : Real) * (q : Real)) :=
        (div_le_iff₀ (mul_pos hNPos hqPos)).1 happrox'
      _ = (N : Real) / u := by
        field_simp [ne_of_gt hqPos, ne_of_gt huPos]
  have hEBound :
      (E.natAbs : Real) ≤
        ((N : Real) / u) * (p : Real) ^ (k - 1) := by
    calc
      (E.natAbs : Real) = |(e₀ : Real)| * (p : Real) ^ (k - 1) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        dsimp only [E]
        push_cast
        rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : Real) ≤ p)]
      _ ≤ ((N : Real) / u) * (p : Real) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right he₀Bound (by positivity)
  have hcCast : (c : ZMod N) = a * r := ZMod.coe_valMinAbs _
  have he₀Cast : (e₀ : ZMod N) =
      -(c : ZMod N) * (q : ZMod N) := by
    dsimp only [e₀]
    push_cast
    simp
  have hECast : (E : ZMod N) =
      (-(c : ZMod N) * (q : ZMod N)) *
        (p : ZMod N) ^ (k - 1) := by
    dsimp only [E]
    push_cast
    rw [he₀Cast]
  have hpCast : (p : ZMod N) = (s : ZMod N) * (q : ZMod N) := Nat.cast_mul s q
  have htarget :
      ((p : ZMod N) ^ k) * a = (E : ZMod N) ∨
        ((p : ZMod N) ^ k) * a = -(E : ZMod N) := by
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ k), pow_succ, hECast, hpCast]
    rcases lemma55_natCast_centeredAbs_eq_or_neg r with hsCast | hsCast
    · right
      rw [hsCast, hcCast]
      ring
    · left
      rw [hsCast, hcCast]
      ring
  have hcenterNat :
      centeredAbs (((p : ZMod N) ^ k) * a) ≤ E.natAbs := by
    rcases htarget with htarget | htarget
    · rw [htarget]
      exact lemma55_centeredAbs_intCast_le E
    · rw [htarget, lemma55_centeredAbs_neg]
      exact lemma55_centeredAbs_intCast_le E
  have hcenterReal :
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs := by
    exact_mod_cast hcenterNat
  have hscaleCompare :
      (u : Real) ^ (-2 * gamma) / 4 ≤ (t : Real) ^ (-gamma) := by
    simpa only [gamma] using lemma55_sqrt_scale_compare hk htOne huOne htFour
  have huFactor :
      ((N : Real) / u) * ((u : Real) ^ (1 - 2 * gamma) / 4) =
        ((u : Real) ^ (-2 * gamma) / 4) * N := by
    rw [show (1 : Real) - 2 * gamma = 1 + -2 * gamma by ring, Real.rpow_add huPos,
      Real.rpow_one]
    field_simp [ne_of_gt huPos]
  have hfinal :
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤
        (t : Real) ^ (-gamma) * N := by
    calc
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs :=
        hcenterReal
      _ ≤ ((N : Real) / u) * (p : Real) ^ (k - 1) := hEBound
      _ ≤ ((N : Real) / u) *
          ((u : Real) ^ (1 - 2 * gamma) / 4) := by
        exact mul_le_mul_of_nonneg_left hpPow (by positivity)
      _ = ((u : Real) ^ (-2 * gamma) / 4) * N := huFactor
      _ ≤ (t : Real) ^ (-gamma) * N :=
        mul_le_mul_of_nonneg_right hscaleCompare (by positivity)
  apply hrecurrence
  exact ⟨p, hpOne, hpSqT, by simpa only [gamma] using hfinal⟩

end LeanProofs.GowersSzemeredi
