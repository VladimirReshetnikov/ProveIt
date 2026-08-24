import GowersSzemeredi.Proofs05MissingInterval
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.NumberTheory.Divisors

/-!
# Audit of the polynomial progression partition in Section 5

The exact-cell, almost-equal partition asserted in the former statement of
Corollary 5.6 is false.  The counterexample below uses the identity polynomial
modulo two.  At the claimed diameter scale every cell must be parity
homogeneous, while the prescribed equal cell size cannot divide the number of
even elements in the interval.

The repaired live target-length statement is the form actually delivered by
the printed induction.  The displayed proof of Lemma 5.5 applies a Fourier
estimate for a set to a polynomial value sequence as if that sequence had no
collisions.  Below we instead use the multiplicity function of that sequence;
its Fourier transform is the required Weyl sum even when values collide.

There is also a quantitative transcription issue in the induction: the first
two occurrences of the leading-coefficient bound must have exponent
`-1 / (k * 2^(k+1))`, not `-1 / (k * 2^(k+2))`, in order for the displayed
choice of the chunk length `u` to yield the following `k+2` exponent.
-/

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
  classical
  let H : Finset (ZMod N) :=
    Finset.univ.filter fun r : ZMod N => K < centeredAbs r
  let T : Finset (Nat × Bool) := Finset.Ioc K N ×ˢ Finset.univ
  have habsN (r : ZMod N) : centeredAbs r ≤ N := by
    exact (ZMod.natAbs_valMinAbs_le r).trans (Nat.div_le_self N 2)
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
      _ ≤ ∑ p ∈ T, (((p.1 : Nat) : Real) ^ 2)⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
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
  rw [fourier, ZMod.dft_apply]
  calc
    ‖∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) • (w x : Complex)‖ ≤
        ∑ x : ZMod N, ‖ZMod.stdAddChar (-(x * r)) • (w x : Complex)‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod N, (w x : Real) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [ZMod.stdAddChar_apply]
    _ = (∑ x : ZMod N, w x : Nat) := by push_cast; rfl

@[simp] private lemma fourier_natWeight_zero {N : Nat} [NeZero N]
    (w : ZMod N → Nat) :
    fourier (fun x => (w x : Complex)) 0 = ((∑ x, w x : Nat) : Complex) := by
  simp [fourier, ZMod.dft_apply]

@[simp] private lemma polynomialPartition_fourier_indicator_zero
    {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    fourier (indicator A) 0 = (A.card : Complex) := by
  classical
  simp [fourier, ZMod.dft_apply, indicator]

private lemma polynomialPartition_fourier_indicator_energy {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2) =
      (N : Real) * A.card := by
  rw [identity_2_3_holds]
  congr 1
  classical
  calc
    (∑ x : ZMod N, ‖indicator A x‖ ^ 2) =
        ∑ x : ZMod N, if x ∈ A then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    _ = A.card := by simp

private lemma weighted_centeredInterval_sub_mem {N L : Nat} [NeZero N]
    {x y : ZMod N} (hx : x ∈ centeredInterval N L)
    (hy : y ∈ centeredInterval N L) :
    x - y ∈ centeredInterval N (L + L) := by
  classical
  simp only [centeredInterval, Finset.mem_image] at hx hy ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a - b, ?_, by push_cast; rfl⟩
  simp only [Finset.mem_Ico] at ha hb ⊢
  constructor <;> (push_cast at *; omega)

private lemma weighted_centeredInterval_card (N L : Nat) [NeZero N]
    (hLN : 2 * L ≤ N) :
    (centeredInterval N L).card = 2 * L := by
  classical
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
  classical
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
    classical
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
  have hfour : 4 * (L + L) ^ 2 ≤ N ^ 2 := by
    calc
      4 * (L + L) ^ 2 = (2 * (L + L)) * (2 * (L + L)) := by ring
      _ ≤ N * N := hsquare
      _ = N ^ 2 := by ring
  have hK4 : 4 ≤ K := by
    dsimp only [K]
    exact (Nat.le_div_iff_mul_le hden).2 hfour
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK4
  have hKmul : K * (L + L) ^ 2 ≤ N ^ 2 := by
    dsimp only [K]
    exact Nat.div_mul_le_self _ _
  have hfloor : N ^ 2 < (K + 1) * (L + L) ^ 2 := by
    exact (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self K)
  have hthree : 3 * N ^ 2 ≤ 4 * K * (L + L) ^ 2 := by
    have hcoef : 3 * (K + 1) ≤ 4 * K := by omega
    calc
      3 * N ^ 2 ≤ 3 * ((K + 1) * (L + L) ^ 2) :=
        Nat.mul_le_mul_left 3 (Nat.le_of_lt hfloor)
      _ = (3 * (K + 1)) * (L + L) ^ 2 := by ring
      _ ≤ (4 * K) * (L + L) ^ 2 :=
        Nat.mul_le_mul_right ((L + L) ^ 2) hcoef
      _ = 4 * K * (L + L) ^ 2 := by ring
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
      polynomialPartition_fourier_indicator_zero, hmass, hIcard]
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
    refine ⟨r, hr0, ?_, le_of_not_gt hlarge⟩
    exact (Nat.cast_le.mpr hrK).trans hKratio
  by_cases ht : t = 0
  · letI : Fact (1 < N) := ⟨hN⟩
    have hhalf : 1 ≤ N / 2 := by omega
    have habs_one : centeredAbs (1 : ZMod N) = 1 := by
      simp [centeredAbs, ZMod.valMinAbs_def_pos, ZMod.val_one N, hhalf]
    have hbad := hlow_coeff (r := (1 : ZMod N)) one_ne_zero
      (by rw [habs_one]; omega)
    have hzero' : (t : Real) * (L + L : Nat) / (4 * N) = 0 := by
      rw [ht]
      norm_num
    rw [hzero'] at hbad
    exact (not_lt_of_ge (norm_nonneg _) hbad).elim
  have htpos : (0 : Real) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  let energyTerm : ZMod N → Real := fun r =>
    ‖fourier (fun x => (w x : Complex)) r‖ *
      ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2
  let low : Finset (ZMod N) :=
    (Finset.univ.erase 0).filter fun r => centeredAbs r ≤ K
  let high : Finset (ZMod N) :=
    (Finset.univ.erase 0).filter fun r => K < centeredAbs r
  have hdisj_low_high : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro r hrl hrh
    have hrle : centeredAbs r ≤ K := (Finset.mem_filter.mp hrl).2
    have hrgt : K < centeredAbs r := (Finset.mem_filter.mp hrh).2
    omega
  have hunion : low ∪ high = Finset.univ.erase (0 : ZMod N) := by
    ext r
    simp only [low, high, Finset.mem_union, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨hr0, _⟩ | ⟨hr0, _⟩) <;> exact hr0
    · intro hr0
      by_cases hrK : centeredAbs r ≤ K
      · exact Or.inl ⟨hr0, hrK⟩
      · exact Or.inr ⟨hr0, Nat.lt_of_not_ge hrK⟩
  have hsplit :
      (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r) =
        (∑ r ∈ low, energyTerm r) + ∑ r ∈ high, energyTerm r := by
    rw [← Finset.sum_union hdisj_low_high, hunion]
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
        rw [polynomialPartition_fourier_indicator_energy, hIcard]
        field_simp [NeZero.ne N]
  have hhigh_eq :
      high = Finset.univ.filter (fun r : ZMod N => K < centeredAbs r) := by
    ext r
    simp only [high, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and]
    constructor
    · exact fun h => h.2
    · intro hr
      refine ⟨?_, hr⟩
      intro hr0
      subst r
      simp only [centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero] at hr
      omega
  have hhigh_point {r : ZMod N} (hr : r ∈ high) :
      energyTerm r ≤
        ((t : Real) * (N : Real) ^ 2 / 4) *
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by
    have hrK : K < centeredAbs r := by
      rw [hhigh_eq] at hr
      exact (Finset.mem_filter.mp hr).2
    have hr0 : r ≠ 0 := by
      rw [hhigh_eq] at hr
      intro hrzero
      subst r
      simp only [centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero] at hrK
      omega
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
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹ := by
        field_simp [ne_of_gt habs]
        ring
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
        exact mul_le_mul_of_nonneg_left (by
          rw [hhigh_eq]
          exact weighted_centered_reciprocal_sq_tail hKpos) (by positivity)
      _ = (t : Real) * ((N : Real) ^ 2 / (2 * K)) := by
        field_simp [show (K : Real) ≠ 0 by positivity]
        ring
      _ ≤ (t : Real) * ((2 / 3 : Real) * (L + L : Nat) ^ 2) :=
        mul_le_mul_of_nonneg_left hscaled_tail htpos.le
      _ = (2 / 3 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by ring
  have hupper :
      (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r) ≤
        (11 / 12 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by
    rw [hsplit]
    calc
      (∑ r ∈ low, energyTerm r) + ∑ r ∈ high, energyTerm r ≤
          (t : Real) * (L + L : Nat) ^ 2 / 4 +
            (2 / 3 : Real) * (t : Real) * (L + L : Nat) ^ 2 :=
        add_le_add hlow_energy hhigh_energy
      _ = (11 / 12 : Real) * (t : Real) * (L + L : Nat) ^ 2 := by ring
  have hlower' :
      (t : Real) * (L + L : Nat) ^ 2 ≤
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r := hlower
  have hmasspos : (0 : Real) < (t : Real) * (L + L : Nat) ^ 2 := by positivity
  nlinarith [hlower'.trans hupper]

/-! The weight used for polynomial recurrence counts occurrences rather than
discarding repeated values.  This is the precise repair of the collision in
the printed proof of Lemma 5.5. -/

private noncomputable def polynomialValueMultiplicity {N : Nat}
    (k t : Nat) (a : ZMod N) (x : ZMod N) : Nat :=
  ((Finset.Icc 1 t).filter fun s : Nat => ((s : ZMod N) ^ k) * a = x).card

private lemma polynomialValueMultiplicity_mass {N k t : Nat} [NeZero N]
    (a : ZMod N) :
    ∑ x : ZMod N, polynomialValueMultiplicity k t a x = t := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := Finset.Icc 1 t) (t := (Finset.univ : Finset (ZMod N)))
    (f := fun s : Nat => ((s : ZMod N) ^ k) * a) (by simp)
  simpa [polynomialValueMultiplicity, Nat.card_Icc] using hfiber.symm

private lemma centeredAbs_le_of_mem_centeredInterval {N M : Nat} [NeZero N]
    (hMN : 2 * M ≤ N) {x : ZMod N} (hx : x ∈ centeredInterval N M) :
    centeredAbs x ≤ M := by
  classical
  simp only [centeredInterval, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  simp only [Finset.mem_Ico] at hz
  by_cases hboundary : z * 2 = -(N : Int)
  · have hNM : N ≤ 2 * M := by
      exact_mod_cast (show (N : Int) ≤ 2 * M by linarith)
    have hhalf : N / 2 ≤ M := by omega
    exact (ZMod.natAbs_valMinAbs_le (z : ZMod N)).trans hhalf
  · have hlower : -(N : Int) < z * 2 := by
      have : -(N : Int) ≤ z * 2 := by
        have hcast : (2 * (M : Nat) : Int) ≤ N := by exact_mod_cast hMN
        linarith
      exact lt_of_le_of_ne this (Ne.symm hboundary)
    have hupper : z * 2 ≤ (N : Int) := by
      have hcast : (2 * (M : Nat) : Int) ≤ N := by exact_mod_cast hMN
      linarith
    have hval : ((z : ZMod N).valMinAbs) = z :=
      (ZMod.valMinAbs_spec (z : ZMod N) z).2
        ⟨rfl, ⟨hlower, hupper⟩⟩
    rw [centeredAbs, hval]
    have hzabs : (z.natAbs : Int) ≤ (M : Int) := by
      by_cases hznonneg : 0 ≤ z
      · rw [Int.natAbs_of_nonneg hznonneg]
        exact le_of_lt hz.2
      · have hznonpos : z ≤ 0 := (lt_of_not_ge hznonneg).le
        rw [Int.ofNat_natAbs_of_nonpos hznonpos]
        linarith [hz.1]
    exact_mod_cast hzabs

private lemma polynomialValueMultiplicity_zero_of_avoids {N k t M : Nat}
    [NeZero N] (a : ZMod N)
    (havoid : ∀ s ∈ Finset.Icc 1 t,
      ((s : ZMod N) ^ k) * a ∉ centeredInterval N M) :
    ∀ x ∈ centeredInterval N M, polynomialValueMultiplicity k t a x = 0 := by
  classical
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
  classical
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
          (((-((s : Int) ^ k) * (a * r).valMinAbs : Int) : ZMod N)) := by
      congr 1
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_natCast,
        ZMod.coe_valMinAbs]
      ring
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

private lemma fourier_polynomialValueMultiplicity_eq_weylSum
    {N k t : Nat} [NeZero N] (a r : ZMod N) :
    fourier (fun x => (polynomialValueMultiplicity k t a x : Complex)) r =
      weylSum (-(a * r).valMinAbs / (N : Real)) k t := by
  rw [fourier_polynomialValueMultiplicity]
  unfold weylSum
  apply Finset.sum_congr rfl
  intro s _
  rw [exponential_polynomial_eq_realExponential]

private theorem polynomial_missing_interval_witness
    {N k t M : Nat} [NeZero N] (a : ZMod N) (gamma : Real)
    (ht : 2 ≤ t) (htN : t ≤ N) (hM : 0 < M) (hMeven : Even M)
    (hMN : 2 * M ≤ N)
    (hMscale : (M : Real) ≤ (t : Real) ^ (-gamma) * N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (t : Real) ^ (-gamma) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤ (N : Real) ^ 2 / (M : Real) ^ 2 ∧
      (t : Real) * M / (4 * N) ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k t‖ := by
  have hN : 1 < N := lt_of_lt_of_le (by omega : 1 < t) htN
  let w : ZMod N → Nat := polynomialValueMultiplicity k t a
  have hmass : ∑ x : ZMod N, w x = t :=
    polynomialValueMultiplicity_mass a
  have havoid : ∀ s ∈ Finset.Icc 1 t,
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
    weighted_missing_interval_fourier N M t w hN hM hMeven hMN hmass hzero
  refine ⟨r, hr0, hrsize, ?_⟩
  rwa [fourier_polynomialValueMultiplicity_eq_weylSum] at hrlarge

private lemma twice_floor_quarter_bounds {x : Real} (hx : 8 ≤ x) :
    let M := 2 * Nat.floor (x / 4)
    0 < M ∧ Even M ∧ (M : Real) ≤ x / 2 ∧ x / 4 ≤ M := by
  let u : Nat := Nat.floor (x / 4)
  have hx0 : 0 ≤ x / 4 := by positivity
  have huUpper : (u : Real) ≤ x / 4 := by
    exact Nat.floor_le hx0
  have huLower : x / 4 < (u : Real) + 1 := by
    exact Nat.lt_floor_add_one (x / 4)
  have huOne : 1 ≤ u := by
    apply Nat.le_floor
    linarith
  dsimp only
  refine ⟨by omega, even_two_mul u, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

private lemma weylThreshold_sixtyFour_le {k : Nat} (hk : 2 ≤ k) :
    64 ≤ weylThreshold k := by
  have hinnerExponent : 3 ≤ 32 * k ^ 2 := by nlinarith
  have houterExponent : 6 ≤ 2 ^ (32 * k ^ 2) := by
    have hpow : 2 ^ 3 ≤ 2 ^ (32 * k ^ 2) :=
      pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : Nat)) hinnerExponent
    norm_num at hpow ⊢
    omega
  have hpow : 2 ^ 6 ≤ 2 ^ (2 ^ (32 * k ^ 2)) :=
    pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : Nat)) houterExponent
  simpa [weylThreshold] using hpow

private lemma recurrenceExponent_nonneg (k : Nat) :
    0 ≤ (((k : Real) * (2 : Real) ^ (k + 1))⁻¹) := by positivity

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

private lemma recurrenceScale_eight_le {k t N : Nat}
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

private lemma recurrenceScale_le_N {k t N : Nat} (ht : 1 ≤ t) :
    (t : Real) ^
      (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N ≤ N := by
  have htOne : (1 : Real) ≤ t := by exact_mod_cast ht
  have hpow :
      (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos htOne
      (neg_nonpos.mpr (recurrenceExponent_nonneg k))
  have hN : (0 : Real) ≤ N := by positivity
  calc
    (t : Real) ^
        (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N ≤ 1 * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ = N := one_mul _

private theorem polynomial_weyl_witness
    {N k t : Nat} [NeZero N] (a : ZMod N)
    (hk : 2 ≤ k) (ht : weylThreshold k ≤ t) (htN : t ≤ N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (t : Real) ^
          (-(((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) * N <
        (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧
      (centeredAbs r : Real) ≤
        16 * (t : Real) ^
          (2 * (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) ∧
      (t : Real) ^
          (1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
        ‖weylSum (-(a * r).valMinAbs / (N : Real)) k t‖ := by
  let gamma : Real := ((k : Real) * (2 : Real) ^ (k + 1))⁻¹
  let scale : Real := (t : Real) ^ (-gamma) * N
  let M : Nat := 2 * Nat.floor (scale / 4)
  have htTwo : 2 ≤ t := by
    exact (by norm_num : 2 ≤ 64).trans
      ((weylThreshold_sixtyFour_le hk).trans ht)
  have hscaleEight : 8 ≤ scale := by
    simpa only [scale, gamma] using recurrenceScale_eight_le hk ht htN
  obtain ⟨hMpos, hMeven, hMupper, hMlower⟩ :=
    twice_floor_quarter_bounds hscaleEight
  have hscaleN : scale ≤ N := by
    simpa only [scale, gamma] using recurrenceScale_le_N (k := k) (N := N)
      (show 1 ≤ t by omega)
  have hMNReal : (2 : Real) * M ≤ N := by
    calc
      (2 : Real) * M ≤ 2 * (scale / 2) := by gcongr
      _ = scale := by ring
      _ ≤ N := hscaleN
  have hMN : 2 * M ≤ N := by exact_mod_cast hMNReal
  have hMscale : (M : Real) ≤ (t : Real) ^ (-gamma) * N := by
    exact hMupper.trans (by linarith [hscaleEight])
  obtain ⟨r, hr0, hrsize, hrlarge⟩ :=
    polynomial_missing_interval_witness a gamma htTwo htN hMpos hMeven hMN
      hMscale (by simpa only [gamma] using hno)
  have htPos : (0 : Real) < t := by positivity
  have hNPos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMPosReal : (0 : Real) < M := by exact_mod_cast hMpos
  have hposPow : (0 : Real) < (t : Real) ^ gamma :=
    Real.rpow_pos_of_pos htPos gamma
  have hnegPow : (0 : Real) < (t : Real) ^ (-gamma) :=
    Real.rpow_pos_of_pos htPos (-gamma)
  have hpowersCancel : (t : Real) ^ gamma * (t : Real) ^ (-gamma) = 1 := by
    rw [← Real.rpow_add htPos]
    simp
  have hNM : (N : Real) ≤ 4 * (t : Real) ^ gamma * M := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower (show 0 ≤ 4 *
      (t : Real) ^ gamma by positivity)
    dsimp only [scale] at hscaled
    have hleft :
        4 * (t : Real) ^ gamma *
            (((t : Real) ^ (-gamma) * N) / 4) = N := by
      calc
        4 * (t : Real) ^ gamma *
            (((t : Real) ^ (-gamma) * N) / 4) =
            ((t : Real) ^ gamma * (t : Real) ^ (-gamma)) * N := by ring
        _ = N := by rw [hpowersCancel, one_mul]
    rw [hleft] at hscaled
    exact hscaled
  have hratio :
      (N : Real) ^ 2 / (M : Real) ^ 2 ≤
        16 * (t : Real) ^ (2 * gamma) := by
    have hsquare : (N : Real) ^ 2 ≤
        (4 * (t : Real) ^ gamma * M) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hNM 2
    have hrpow :
        (t : Real) ^ (2 * gamma) = ((t : Real) ^ gamma) ^ 2 := by
      rw [show 2 * gamma = gamma + gamma by ring, Real.rpow_add htPos]
      ring
    rw [hrpow]
    apply (div_le_iff₀ (sq_pos_of_pos hMPosReal)).2
    calc
      (N : Real) ^ 2 ≤ (4 * (t : Real) ^ gamma * M) ^ 2 := hsquare
      _ = (16 * ((t : Real) ^ gamma) ^ 2) * M ^ 2 := by ring
  have hlower :
      (t : Real) ^ (1 - gamma) / 16 ≤
        (t : Real) * M / (4 * N) := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower
      (show 0 ≤ (t : Real) / (4 * N) by positivity)
    have hcombine :
        (t : Real) * ((t : Real) ^ (-gamma) * N) / (16 * N) =
          (t : Real) ^ (1 - gamma) / 16 := by
      rw [show 1 - gamma = 1 + -gamma by ring, Real.rpow_add htPos,
        Real.rpow_one]
      field_simp [ne_of_gt hNPos]
    dsimp only [scale] at hscaled
    calc
      (t : Real) ^ (1 - gamma) / 16 =
          (t : Real) * ((t : Real) ^ (-gamma) * N) / (16 * N) :=
        hcombine.symm
      _ = ((t : Real) / (4 * N)) *
          (((t : Real) ^ (-gamma) * N) / 4) := by ring
      _ ≤ ((t : Real) / (4 * N)) * M := hscaled
      _ = (t : Real) * M / (4 * N) := by ring
  refine ⟨r, hr0, ?_, ?_⟩
  · exact hrsize.trans (by simpa only [gamma] using hratio)
  · have hlower' :
        (t : Real) ^
            (1 - (((k : Real) * (2 : Real) ^ (k + 1))⁻¹)) / 16 ≤
          (t : Real) * M / (4 * N) := by
      simpa only [gamma] using hlower
    exact hlower'.trans hrlarge

/-!
The arithmetic part of the counterexample is developed for an abstract odd
integer `Q`.  This is intentional: reducing the displayed threshold
`2^(2^40)` during elaboration is both unnecessary and very expensive.  The
final specialization will take `Q = 2 * polynomialPartitionThreshold 1 + 1`.
-/

private def cor56CounterR (Q : Nat) : Nat := Q ^ 16

private def cor56CounterM (Q : Nat) : Nat := Q ^ 15

private lemma cor56Counter_constant : polynomialPartitionConstant 1 = 16 := by
  norm_num [polynomialPartitionConstant]

private lemma polynomialPartitionThreshold_pos (k : Nat) :
    0 < polynomialPartitionThreshold k := by
  unfold polynomialPartitionThreshold
  exact pow_pos (by norm_num) _

private lemma cor56Counter_threshold_lt_r {Q : Nat}
    (hQ : polynomialPartitionThreshold 1 < Q) :
    polynomialPartitionThreshold 1 < cor56CounterR Q := by
  have hqOne : 1 ≤ Q := by
    have := polynomialPartitionThreshold_pos 1
    omega
  have hqPow : Q ≤ Q ^ 16 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hqOne (by norm_num : (1 : Nat) ≤ 16)
  exact hQ.trans_le hqPow

private lemma cor56Counter_m_le_r {Q : Nat} (hQ : 1 ≤ Q) :
    cor56CounterM Q ≤ cor56CounterR Q := by
  unfold cor56CounterM cor56CounterR
  exact pow_le_pow_right₀ hQ (by norm_num)

private lemma cor56Counter_scale_lower {Q : Nat} (hQ : 0 < Q) :
    (cor56CounterR Q : Real) ^
        (1 - (polynomialPartitionConstant 1 : Real)⁻¹) ≤ cor56CounterM Q := by
  rw [cor56Counter_constant]
  unfold cor56CounterR cor56CounterM
  push_cast
  have hq : (0 : Real) ≤ Q := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num [Real.rpow_natCast]

private lemma cor56Counter_scale_lt_one {Q : Nat} (hQ : 2 < Q) :
    (cor56CounterR Q : Real) ^
        (-(polynomialPartitionConstant 1 : Real)⁻¹) * 2 < 1 := by
  rw [cor56Counter_constant]
  unfold cor56CounterR
  push_cast
  have hq : (0 : Real) ≤ Q := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  have hmul : ((16 : Nat) : Real) * (-(16 : Real)⁻¹) = -1 := by norm_num
  rw [hmul, Real.rpow_neg_one]
  have hqpos : (0 : Real) < Q := by positivity
  have hqreal : (2 : Real) < Q := by exact_mod_cast hQ
  simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hqpos).2 hqreal

private lemma modInterval_one_carrier {N : Nat} (a : ZMod N) :
    (modInterval N a 1).carrier = {a} := by
  classical
  ext x
  simp [modInterval, ModAP.carrier]

private lemma diameterAtMostReal_subsingleton_of_lt_one {N : Nat}
    {A : Finset (ZMod N)} {s : Real} (hA : diameterAtMostReal A s) (hs : s < 1)
    {x y : ZMod N} (hx : x ∈ A) (hy : y ∈ A) : x = y := by
  obtain ⟨d, ⟨a, ha⟩, hd⟩ := hA
  have hdReal : (d : Real) < 1 := hd.trans_lt hs
  have hdNat : d < 1 := by exact_mod_cast hdReal
  have hdZero : d = 0 := by omega
  subst d
  have hxa : x ∈ ({a} : Finset (ZMod N)) := by
    rw [← modInterval_one_carrier]
    exact ha hx
  have hya : y ∈ ({a} : Finset (ZMod N)) := by
    rw [← modInterval_one_carrier]
    exact ha hy
  exact (mem_singleton.mp hxa).trans (mem_singleton.mp hya).symm

private lemma identity_polynomialOn_zmod_two :
    PolynomialOn 1 Finset.univ (fun x : ZMod 2 => x) := by
  refine ⟨![0, 1], ?_⟩
  intro x _
  simp [Fin.sum_univ_two]

private lemma balanced_lengths_eq_average {m q : Nat} (f : Fin m → Nat)
    (hsum : ∑ i, f i = m * q) (hbalanced : ∀ i j, f i ≤ f j + 1) :
    ∀ i, f i = q := by
  intro i
  rcases lt_trichotomy (f i) q with hlt | heq | hgt
  · have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), f j ≤ q := by
      intro j _
      exact (hbalanced j i).trans (by omega)
    have hsums : ∑ j, f j = ∑ _j : Fin m, q := by
      simpa using hsum
    exact (sum_eq_sum_iff_of_le hle).mp hsums i (mem_univ i)
  · exact heq
  · have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), q ≤ f j := by
      intro j _
      have := hbalanced i j
      omega
    have hsums : ∑ _j : Fin m, q = ∑ j, f j := by
      simpa using hsum.symm
    exact ((sum_eq_sum_iff_of_le hle).mp hsums i (mem_univ i)).symm

private lemma isPartition_filter {X : Type*} [DecidableEq X] {m : Nat}
    {P : Fin m → Finset X} {S : Finset X} (hP : IsPartition P S)
    (p : X → Prop) [DecidablePred p] :
    IsPartition (fun i => (P i).filter p) (S.filter p) := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨hxS, hpx⟩ := mem_filter.mp hx
      obtain ⟨i, hxi⟩ := (hP.1 x).mp hxS
      exact ⟨i, mem_filter.mpr ⟨hxi, hpx⟩⟩
    · rintro ⟨i, hxi⟩
      obtain ⟨hxiP, hpx⟩ := mem_filter.mp hxi
      exact mem_filter.mpr ⟨(hP.1 x).mpr ⟨i, hxiP⟩, hpx⟩
  · intro i j hij
    exact (hP.2 i j hij).mono (filter_subset p (P i)) (filter_subset p (P j))

private lemma card_filter_even_range : ∀ n : Nat,
    ((Finset.range n).filter Even).card = (n + 1) / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [range_add_one, filter_insert]
      by_cases hn : Even n
      · rw [if_pos hn, card_insert_of_notMem]
        · rw [ih]
          obtain ⟨a, rfl⟩ := hn
          omega
        · simp
      · rw [if_neg hn, ih]
        obtain ⟨a, rfl⟩ := Nat.not_even_iff_odd.mp hn
        omega

private lemma cor56Counter_r_eq_m_mul_q (Q : Nat) :
    cor56CounterR Q = cor56CounterM Q * Q := by
  unfold cor56CounterR cor56CounterM
  rw [show 16 = 15 + 1 by norm_num, pow_succ]

private lemma exists_large_odd (T : Nat) (hT : 0 < T) :
    ∃ Q : Nat, 2 < Q ∧ Odd Q ∧ T < Q := by
  refine ⟨2 * T + 1, ?_, ⟨T, by omega⟩, ?_⟩ <;> omega

/-- The former exact-cell-count formulation of Corollary 5.6.  It is retained
only so that the concrete counterexample remains checkable after the live
Section 5 statement is repaired. -/
def corollary_5_6_exact_cell_legacy : Prop :=
  ∀ (N k r m : Nat) [NeZero N] (phi : ZMod N → ZMod N),
    1 ≤ k → PolynomialOn k Finset.univ phi →
    polynomialPartitionThreshold k < r →
    (r : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) ≤ m → m ≤ r →
      ∃ P : Fin m → NatAP,
        IsNatAPPartition P (Finset.range r) ∧
        (∀ j, (P j).IsProper) ∧ NatAPLengthsDifferAtMostOne P ∧
        ∀ j, diameterAtMostReal
          ((P j).carrier.image fun x : Nat => phi (x : ZMod N))
          ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N)

/-- A parameterized counterexample to the exact-cell, balanced version of
Corollary 5.6.  Keeping `Q` abstract prevents Lean from evaluating the
doubly-exponential numerical threshold. -/
private theorem corollary_5_6_counterexample_of_Q (Q : Nat) (hQ : 2 < Q)
    (hQodd : Odd Q) (hthreshold : polynomialPartitionThreshold 1 < Q) :
    ¬ corollary_5_6_exact_cell_legacy := by
  classical
  intro h56
  unfold corollary_5_6_exact_cell_legacy at h56
  obtain ⟨P, hpartition, hproper, hbalanced, hdiameter⟩ :=
    h56 2 1 (cor56CounterR Q) (cor56CounterM Q) (fun x : ZMod 2 => x)
      (by norm_num) identity_polynomialOn_zmod_two
      (cor56Counter_threshold_lt_r hthreshold)
      (cor56Counter_scale_lower (by omega))
      (cor56Counter_m_le_r (by omega))
  have hsumLengths :
      ∑ j, (P j).length = cor56CounterR Q := by
    calc
      ∑ j, (P j).length = ∑ j, (P j).carrier.card := by
        apply sum_congr rfl
        intro j _
        exact (hproper j).2.symm
      _ = (Finset.range (cor56CounterR Q)).card := hpartition.sum_card
      _ = cor56CounterR Q := card_range _
  have hlength : ∀ j, (P j).length = Q := by
    apply balanced_lengths_eq_average (fun j => (P j).length)
    · exact hsumLengths.trans (cor56Counter_r_eq_m_mul_q Q)
    · exact hbalanced
  have hscale :
      (cor56CounterR Q : Real) ^
          (-(polynomialPartitionConstant 1 : Real)⁻¹) * 2 < 1 :=
    cor56Counter_scale_lt_one hQ
  have hsameCast (j : Fin (cor56CounterM Q)) {x y : Nat}
      (hx : x ∈ (P j).carrier) (hy : y ∈ (P j).carrier) :
      (x : ZMod 2) = (y : ZMod 2) := by
    apply diameterAtMostReal_subsingleton_of_lt_one (hdiameter j) hscale
    · exact mem_image.mpr ⟨x, hx, rfl⟩
    · exact mem_image.mpr ⟨y, hy, rfl⟩
  have hsameParity (j : Fin (cor56CounterM Q)) {x y : Nat}
      (hx : x ∈ (P j).carrier) (hy : y ∈ (P j).carrier) :
      Even x ↔ Even y := by
    have hxy := hsameCast j hx hy
    constructor
    · intro hxeven
      have hxzero : (x : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr hxeven
      exact ZMod.natCast_eq_zero_iff_even.mp (hxy.symm.trans hxzero)
    · intro hyeven
      have hyzero : (y : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr hyeven
      exact ZMod.natCast_eq_zero_iff_even.mp (hxy.trans hyzero)
  have hcellDvd (j : Fin (cor56CounterM Q)) :
      Q ∣ ((P j).carrier.filter Even).card := by
    by_cases hex : ∃ x ∈ (P j).carrier, Even x
    · obtain ⟨x, hx, hxeven⟩ := hex
      have hfilter : (P j).carrier.filter Even = (P j).carrier := by
        apply filter_eq_self.mpr
        intro y hy
        exact (hsameParity j hx hy).mp hxeven
      rw [hfilter, (hproper j).2, hlength j]
    · have hfilter : (P j).carrier.filter Even = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro x hx hxeven
        exact hex ⟨x, hx, hxeven⟩
      rw [hfilter]
      simp
  have hevenPartition :
      IsPartition (fun j => (P j).carrier.filter Even)
        ((Finset.range (cor56CounterR Q)).filter Even) :=
    isPartition_filter hpartition Even
  have hglobalDvd :
      Q ∣ ((Finset.range (cor56CounterR Q)).filter Even).card := by
    rw [← hevenPartition.sum_card]
    exact Finset.dvd_sum fun j _ => hcellDvd j
  rw [card_filter_even_range] at hglobalDvd
  have hrOdd : Odd (cor56CounterR Q) := by
    exact hQodd.pow
  have hrSuccEven : Even (cor56CounterR Q + 1) := hrOdd.add_one
  have hQdvdSucc : Q ∣ cor56CounterR Q + 1 := by
    have hmul := hglobalDvd.mul_right 2
    rwa [Nat.div_two_mul_two_of_even hrSuccEven] at hmul
  have hQdvdR : Q ∣ cor56CounterR Q := by
    unfold cor56CounterR
    exact dvd_pow_self Q (by norm_num)
  have hQdvdOne : Q ∣ 1 := by
    simpa using Nat.dvd_sub hQdvdSucc hQdvdR
  have hQone : Q = 1 := Nat.dvd_one.mp hQdvdOne
  omega

/-- The former exact-cell statement of Corollary 5.6 is false.  The
obstruction already occurs for a linear polynomial modulo two. -/
theorem corollary_5_6_exact_partition_counterexample :
    ¬ corollary_5_6_exact_cell_legacy := by
  obtain ⟨Q, hQ, hQodd, hthreshold⟩ :=
    exists_large_odd (polynomialPartitionThreshold 1)
      (polynomialPartitionThreshold_pos 1)
  exact corollary_5_6_counterexample_of_Q Q hQ hQodd hthreshold

end LeanProofs.GowersSzemeredi
