import GowersSzemeredi.Proofs05FourierInterval
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.Lemmas

/-!
# A missing-interval Fourier coefficient

This module proves Gowers's Lemma 5.2.  Its quantitative ingredient is a
reciprocal-square tail estimate for the centered representatives of `ZMod N`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def centeredCode {N : Nat} (r : ZMod N) : Nat × Bool :=
  (centeredAbs r, decide (0 ≤ r.valMinAbs))

private lemma centeredCode_injective {N : Nat} :
    Function.Injective (centeredCode (N := N)) := by
  intro a b hab
  have habs : a.valMinAbs.natAbs = b.valMinAbs.natAbs := by
    simpa only [centeredCode, centeredAbs] using congrArg Prod.fst hab
  have hsign : decide (0 ≤ a.valMinAbs) = decide (0 ≤ b.valMinAbs) := by
    simpa only [centeredCode] using congrArg Prod.snd hab
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

private lemma centered_reciprocal_sq_tail {N K : Nat} [NeZero N]
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
  · have hcode_mem : ∀ r ∈ H, centeredCode r ∈ T := by
      intro r hr
      have hrK : K < centeredAbs r := (Finset.mem_filter.mp hr).2
      simp only [T, Finset.mem_product, Finset.mem_Ioc, Finset.mem_univ,
        and_true, centeredCode]
      exact ⟨hrK, habsN r⟩
    have himage : H.image centeredCode ⊆ T := by
      intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact hcode_mem r hr
    calc
      (∑ r ∈ (Finset.univ.filter fun r : ZMod N => K < centeredAbs r),
          (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) =
          ∑ p ∈ H.image centeredCode, (((p.1 : Nat) : Real) ^ 2)⁻¹ := by
            change (∑ r ∈ H, (((centeredAbs r : Nat) : Real) ^ 2)⁻¹) = _
            symm
            rw [Finset.sum_image]
            · rfl
            · exact centeredCode_injective.injOn
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

private lemma fourier_indicator_norm_le_card' {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ ≤ A.card := by
  classical
  rw [fourier, ZMod.dft_apply]
  calc
    ‖∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) • indicator A x‖ ≤
        ∑ x : ZMod N, ‖ZMod.stdAddChar (-(x * r)) • indicator A x‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod N, if x ∈ A then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [indicator, hx, ZMod.stdAddChar_apply]
    _ = A.card := by simp

@[simp] private lemma fourier_indicator_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    fourier (indicator A) 0 = (A.card : Complex) := by
  classical
  simp [fourier, ZMod.dft_apply, indicator]

private lemma fourier_indicator_energy {N : Nat} [NeZero N]
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

private lemma centeredInterval_sub_mem {N L : Nat} [NeZero N]
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

private lemma centeredInterval_card' (N L : Nat) [NeZero N]
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

private lemma correlation_centeredInterval_eq_zero {N L : Nat} [NeZero N]
    (A : Finset (ZMod N))
    (hdisj : Disjoint A (centeredInterval N (L + L)))
    {a : ZMod N} (ha : a ∈ A) :
    correlation (indicator (centeredInterval N L))
      (indicator (centeredInterval N L)) a = 0 := by
  classical
  unfold correlation
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ centeredInterval N L
  · have hxa : x - a ∉ centeredInterval N L := by
      intro hmem
      have haBig : a ∈ centeredInterval N (L + L) := by
        have hsub := centeredInterval_sub_mem hx hmem
        convert hsub using 1
        abel
      exact Finset.disjoint_left.mp hdisj ha haBig
    simp [indicator, hx, hxa]
  · simp [indicator, hx]

private lemma fourier_energy_relation {N L : Nat} [NeZero N]
    (A : Finset (ZMod N))
    (hdisj : Disjoint A (centeredInterval N (L + L))) :
    (∑ r : ZMod N, fourier (indicator A) r *
      ((‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 : Real) : Complex)) = 0 := by
  let I : ZMod N → Complex := indicator (centeredInterval N L)
  have hparse := identity_2_2_holds N (indicator A) (correlation I I)
  have hright :
      (∑ s : ZMod N, indicator A s * star (correlation I I s)) = 0 := by
    classical
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s ∈ A
    · rw [correlation_centeredInterval_eq_zero A hdisj hs]
      simp
    · simp [indicator, hs]
  rw [hright, mul_zero] at hparse
  rw [← hparse]
  apply Finset.sum_congr rfl
  intro r _
  rw [identity_2_1_holds N I I r]
  simp only [star_mul, star_star]
  congr 1
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]

/-- **Lemma 5.2.** If `A` misses a centered interval, the Fejér-kernel
identity forces a large nonzero Fourier coefficient at low frequency. -/
theorem lemma_5_2_holds : lemma_5_2 := by
  intro N M t _ A hN hM hEven hMN hcard hdisj
  obtain ⟨L, rfl⟩ := hEven
  have hL : 0 < L := by omega
  have hM0 : 0 < L + L := by omega
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
    fourier (indicator A) r *
      ((‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 : Real) : Complex)
  have hrelation : ∑ r : ZMod N, term r = 0 := by
    simpa only [term] using fourier_energy_relation A hdisj
  have hIcard : (centeredInterval N L).card = L + L := by
    simpa [two_mul] using centeredInterval_card' N L hIL
  have hterm_zero : term 0 =
      (((t : Real) * (L + L : Nat) ^ 2 : Real) : Complex) := by
    have hnorm : ‖(((L + L : Nat) : Complex))‖ = ((L + L : Nat) : Real) := by
      rw [Complex.norm_natCast]
    simp only [term, fourier_indicator_zero, hcard, hIcard]
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
          ‖fourier (indicator A) r‖ *
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
          ‖fourier (indicator A) r‖ *
            ‖fourier (indicator (centeredInterval N L)) r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [term, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
  by_contra hnot
  have hlow_coeff {r : ZMod N} (hr0 : r ≠ 0)
      (hrK : centeredAbs r ≤ K) :
      ‖fourier (indicator A) r‖ <
        (t : Real) * (L + L : Nat) / (4 * N) := by
    by_contra hlarge
    apply hnot
    refine ⟨r, bne_iff_ne.mpr hr0, ?_, le_of_not_gt hlarge⟩
    exact (Nat.cast_le.mpr hrK).trans hKratio
  by_cases ht : t = 0
  ·
    letI : Fact (1 < N) := ⟨hN⟩
    have hhalf : 1 ≤ N / 2 := by omega
    have habs_one : centeredAbs (1 : ZMod N) = 1 := by
      simp [centeredAbs, ZMod.valMinAbs_def_pos, ZMod.val_one N, hhalf]
    have hbad := hlow_coeff (r := (1 : ZMod N)) one_ne_zero
      (by rw [habs_one]; omega)
    have hzero : (t : Real) * (L + L : Nat) / (4 * N) = 0 := by
      rw [ht]
      norm_num
    rw [hzero] at hbad
    exact (not_lt_of_ge (norm_nonneg _) hbad).elim
  have htpos : (0 : Real) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  let energyTerm : ZMod N → Real := fun r =>
    ‖fourier (indicator A) r‖ *
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
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun _ _ _ => sq_nonneg _)
      _ = (t : Real) * (L + L : Nat) ^ 2 / 4 := by
        rw [fourier_indicator_energy, hIcard]
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
    have habs : (0 : Real) < centeredAbs r := by exact_mod_cast hKpos.trans hrK
    have hA : ‖fourier (indicator A) r‖ ≤ (t : Real) := by
      rw [← hcard]
      exact fourier_indicator_norm_le_card' A r
    have hI := (lemma_5_1_holds N L hIL r).2 (bne_iff_ne.mpr hr0)
    dsimp only [energyTerm]
    calc
      ‖fourier (indicator A) r‖ *
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
          exact centered_reciprocal_sq_tail hKpos) (by positivity)
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
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)), energyTerm r := by
    exact hlower
  have hmass : (0 : Real) < (t : Real) * (L + L : Nat) ^ 2 := by positivity
  nlinarith [hlower'.trans hupper]

end LeanProofs.GowersSzemeredi
