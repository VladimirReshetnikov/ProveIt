import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs05FourierInterval
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Int.Lemmas

/-!
# Interval discrepancy from degree-one uniformity

This module proves the corrected form of Gowers's Lemma 3.5.  Two omissions in the printed
argument matter formally: a modular interval cannot have length greater than the modulus, and the
claimed constant-one `L^(4/3)` Fourier estimate is false.  The integral test gives a uniform
constant four for that Fourier mass and hence the safe discrepancy constant three used in the
statement catalogue.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod ComplexConjugate
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma modInterval_param_injective {N M : Nat} [NeZero N]
    (b : ZMod N) (hMN : M <= N) :
    Function.Injective (fun i : Fin M => b + (i : Nat)) := by
  intro i j hij
  apply Fin.ext
  have hcast : ((i : Nat) : ZMod N) = (j : Nat) := add_left_cancel hij
  have hmod := (ZMod.natCast_eq_natCast_iff' (i : Nat) (j : Nat) N).mp hcast
  have hiN : (i : Nat) < N := lt_of_lt_of_le i.isLt hMN
  have hjN : (j : Nat) < N := lt_of_lt_of_le j.isLt hMN
  simpa [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] using hmod

private lemma modInterval_card {N M : Nat} [NeZero N]
    (b : ZMod N) (hMN : M <= N) :
    (modInterval N b M).carrier.card = M := by
  classical
  simp only [modInterval, ModAP.carrier, mul_one]
  rw [Finset.card_image_iff.mpr (modInterval_param_injective b hMN).injOn]
  exact Fintype.card_fin M

private lemma fourier_indicator_modInterval_eq_fin_sum {N M : Nat} [NeZero N]
    (b r : ZMod N) (hMN : M <= N) :
    fourier (indicator (modInterval N b M).carrier) r =
      ∑ i : Fin M, ZMod.stdAddChar (-((b + ((i : Nat) : ZMod N)) * r)) := by
  classical
  rw [fourier, ZMod.dft_apply]
  simp only [indicator, smul_eq_mul]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.filter_univ_mem]
  rw [modInterval, ModAP.carrier]
  simp only [mul_one]
  exact Finset.sum_image
    (f := fun j : ZMod N => ZMod.stdAddChar (-(j * r)))
    (g := fun i : Fin M => b + ((i : Nat) : ZMod N))
    (modInterval_param_injective b hMN).injOn

private lemma fin_character_eq_pow {N M : Nat} [NeZero N]
    (r : ZMod N) (i : Fin M) :
    ZMod.stdAddChar (-(((i : Nat) : ZMod N) * r)) =
      (ZMod.stdAddChar (-r)) ^ (i : Nat) := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]
  ring

private lemma norm_fin_character_sum_le {N M : Nat} [NeZero N]
    (r : ZMod N) (hr : r != 0) :
    ‖∑ i : Fin M, ZMod.stdAddChar (-(((i : Nat) : ZMod N) * r))‖ <=
      2 / ‖ZMod.stdAddChar (-r) - 1‖ := by
  let q : Complex := ZMod.stdAddChar (-r)
  have hr' : r ≠ 0 := bne_iff_ne.mp hr
  have hq1 : q ≠ 1 := by
    intro h
    have hneg : -r = 0 := ZMod.injective_stdAddChar (by simpa [q] using h)
    exact hr' (neg_eq_zero.mp hneg)
  simp_rw [fin_character_eq_pow]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hq1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖q ^ M - 1‖ <= ‖q ^ M‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, AddChar.norm_apply]; norm_num

private lemma fourier_modInterval_decay {N M : Nat} [NeZero N]
    (b r : ZMod N) (hMN : M <= N) (hr : r != 0) :
    ‖fourier (indicator (modInterval N b M).carrier) r‖ <=
      (N : Real) / (2 * centeredAbs r) := by
  have hr' : r ≠ 0 := bne_iff_ne.mp hr
  have habsNat : 0 < centeredAbs r := by
    rw [centeredAbs, Int.natAbs_pos]
    exact fun h => hr' ((ZMod.valMinAbs_eq_zero r).mp h)
  have habs : (0 : Real) < centeredAbs r := by exact_mod_cast habsNat
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdenom : 0 < ‖ZMod.stdAddChar (-r) - 1‖ := by
    rw [norm_pos_iff]
    apply sub_ne_zero.mpr
    intro hchar
    have hneg : -r = 0 := ZMod.injective_stdAddChar (by simpa using hchar)
    exact hr' (neg_eq_zero.mp hneg)
  rw [fourier_indicator_modInterval_eq_fin_sum b r hMN]
  calc
    ‖∑ i : Fin M, ZMod.stdAddChar (-((b + ((i : Nat) : ZMod N)) * r))‖ =
        ‖ZMod.stdAddChar (-(b * r)) *
          ∑ i : Fin M, ZMod.stdAddChar (-(((i : Nat) : ZMod N) * r))‖ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ‖∑ i : Fin M, ZMod.stdAddChar (-(((i : Nat) : ZMod N) * r))‖ := by
      rw [norm_mul, AddChar.norm_apply, one_mul]
    _ <= 2 / ‖ZMod.stdAddChar (-r) - 1‖ := norm_fin_character_sum_le r hr
    _ <= (N : Real) / (2 * centeredAbs r) := by
      apply (div_le_div_iff₀ hdenom (mul_pos (by norm_num) habs)).2
      have hlower := character_denominator_lower_bound r
      have hscaled := (div_le_iff₀ hN).mp hlower
      nlinarith

private def intervalCenteredCode {N : Nat} (r : ZMod N) : Nat × Bool :=
  (centeredAbs r, decide (0 <= r.valMinAbs))

private lemma intervalCenteredCode_injective {N : Nat} :
    Function.Injective (intervalCenteredCode (N := N)) := by
  intro a b hab
  have habs : a.valMinAbs.natAbs = b.valMinAbs.natAbs := by
    simpa only [intervalCenteredCode, centeredAbs] using congrArg Prod.fst hab
  have hsign : decide (0 <= a.valMinAbs) = decide (0 <= b.valMinAbs) := by
    simpa only [intervalCenteredCode] using congrArg Prod.snd hab
  apply ZMod.injective_valMinAbs
  by_cases ha : 0 <= a.valMinAbs
  · have hb : 0 <= b.valMinAbs := by
      have : decide (0 <= b.valMinAbs) = true := by rw [← hsign]; simp [ha]
      simpa using this
    exact (Int.natAbs_inj_of_nonneg_of_nonneg ha hb).mp habs
  · have ha' : a.valMinAbs <= 0 := (lt_of_not_ge ha).le
    have hb : b.valMinAbs <= 0 := by
      have : decide (0 <= b.valMinAbs) = false := by rw [← hsign]; simp [ha]
      exact (lt_of_not_ge (by simpa using this)).le
    exact (Int.natAbs_inj_of_nonpos_of_nonpos ha' hb).mp habs

private lemma sum_nat_inv_four_thirds_le_four (L : Nat) :
    (∑ t ∈ Finset.Icc 1 L, (t : Real) ^ (-(4 / 3 : Real))) <= 4 := by
  by_cases hL0 : L = 0
  · simp [hL0]
  have hL : 1 <= L := Nat.one_le_iff_ne_zero.mpr hL0
  have hanti : AntitoneOn (fun x : Real => x ^ (-(4 / 3 : Real))) (Set.Icc 1 L) :=
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by norm_num)).antitoneOn.mono (by
      intro x hx
      exact lt_of_lt_of_le zero_lt_one hx.1)
  have htail :
      (∑ t ∈ Finset.Ico 1 L, ((t + 1 : Nat) : Real) ^ (-(4 / 3 : Real))) <= 3 := by
    calc
      (∑ t ∈ Finset.Ico 1 L, ((t + 1 : Nat) : Real) ^ (-(4 / 3 : Real))) <=
          ∫ x in (1 : Real)..(L : Real), x ^ (-(4 / 3 : Real)) :=
        by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (AntitoneOn.sum_le_integral_Ico
              (f := fun x : Real => x ^ (-(4 / 3 : Real))) (a := 1) (b := L) hL
              (by simpa only [Nat.cast_one] using hanti))
      _ = 3 * (1 - (L : Real) ^ (-(1 / 3 : Real))) := by
        rw [integral_rpow]
        · norm_num
          ring
        · right
          constructor
          · norm_num
          · rw [Set.uIcc_of_le (by exact_mod_cast hL)]
            simp
      _ <= 3 := by
        have := Real.rpow_nonneg (Nat.cast_nonneg L) (-(1 / 3 : Real))
        linarith
  rw [← Finset.sum_erase_add (Finset.Icc 1 L)
    (fun t : Nat => (t : Real) ^ (-(4 / 3 : Real))) (Finset.left_mem_Icc.mpr hL)]
  simp only [Finset.Icc_erase_left, Nat.cast_one, Real.one_rpow]
  have hrewrite :
      (∑ t ∈ Finset.Ioc 1 L, (t : Real) ^ (-(4 / 3 : Real))) =
        ∑ t ∈ Finset.Ico 1 L, ((t + 1 : Nat) : Real) ^ (-(4 / 3 : Real)) := by
    rw [show Finset.Ioc 1 L = Finset.Ico 2 (L + 1) by ext t; simp; omega]
    rw [← Finset.sum_Ico_add' (fun t : Nat => (t : Real) ^ (-(4 / 3 : Real))) 1 L
      (c := 1)]
  rw [hrewrite]
  linarith

private lemma sum_centeredAbs_inv_four_thirds_le_eight {N : Nat} [NeZero N] :
    (∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      (centeredAbs r : Real) ^ (-(4 / 3 : Real))) <= 8 := by
  classical
  let H : Finset (ZMod N) := Finset.univ.erase 0
  let T : Finset (Nat × Bool) := Finset.Icc 1 N ×ˢ Finset.univ
  have habsN (r : ZMod N) : centeredAbs r <= N :=
    (ZMod.natAbs_valMinAbs_le r).trans (Nat.div_le_self N 2)
  have hcode_mem : ∀ r ∈ H, intervalCenteredCode r ∈ T := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have habs0 : 0 < centeredAbs r := by
      rw [centeredAbs, Int.natAbs_pos]
      exact fun h => hr0 ((ZMod.valMinAbs_eq_zero r).mp h)
    simp only [T, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true,
      intervalCenteredCode]
    exact ⟨habs0, habsN r⟩
  have himage : H.image intervalCenteredCode ⊆ T := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact hcode_mem r hr
  calc
    (∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        (centeredAbs r : Real) ^ (-(4 / 3 : Real))) =
        ∑ p ∈ H.image intervalCenteredCode,
          (p.1 : Real) ^ (-(4 / 3 : Real)) := by
      change (∑ r ∈ H, (centeredAbs r : Real) ^ (-(4 / 3 : Real))) = _
      symm
      rw [Finset.sum_image]
      · rfl
      · exact intervalCenteredCode_injective.injOn
    _ <= ∑ p ∈ T, (p.1 : Real) ^ (-(4 / 3 : Real)) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = 2 * ∑ t ∈ Finset.Icc 1 N, (t : Real) ^ (-(4 / 3 : Real)) := by
      simp only [T, Finset.sum_product, Finset.sum_const, Finset.card_univ,
        Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
      rw [Finset.mul_sum]
    _ <= 2 * 4 := mul_le_mul_of_nonneg_left (sum_nat_inv_four_thirds_le_four N) (by norm_num)
    _ = 8 := by norm_num

private lemma interval_decay_rpow_bound {N M : Nat} [NeZero N]
    (b r : ZMod N) (hMN : M <= N) (hr : r != 0) :
    ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real) <=
      ((N : Real) ^ (4 / 3 : Real) / 2) *
        (centeredAbs r : Real) ^ (-(4 / 3 : Real)) := by
  have habsNat : 0 < centeredAbs r := by
    rw [centeredAbs, Int.natAbs_pos]
    exact fun h => (bne_iff_ne.mp hr) ((ZMod.valMinAbs_eq_zero r).mp h)
  have habs : (0 : Real) < centeredAbs r := by exact_mod_cast habsNat
  have hN : (0 : Real) <= N := by positivity
  calc
    ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real) <=
        ((N : Real) / (2 * centeredAbs r)) ^ (4 / 3 : Real) :=
      Real.rpow_le_rpow (norm_nonneg _) (fourier_modInterval_decay b r hMN hr) (by norm_num)
    _ = ((N : Real) ^ (4 / 3 : Real) / (2 : Real) ^ (4 / 3 : Real)) *
        (centeredAbs r : Real) ^ (-(4 / 3 : Real)) := by
      rw [Real.div_rpow hN (by positivity), Real.mul_rpow (by norm_num) habs.le,
        Real.rpow_neg habs.le]
      have htwoPow : (2 : Real) ^ (4 / 3 : Real) ≠ 0 := by positivity
      have habsPow : (centeredAbs r : Real) ^ (4 / 3 : Real) ≠ 0 := by positivity
      field_simp [htwoPow, habsPow]
    _ <= ((N : Real) ^ (4 / 3 : Real) / 2) *
        (centeredAbs r : Real) ^ (-(4 / 3 : Real)) := by
      have htwo : (2 : Real) <= 2 ^ (4 / 3 : Real) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
            (by norm_num : (1 : Real) <= 4 / 3)
      have hcoef : (N : Real) ^ (4 / 3 : Real) / (2 : Real) ^ (4 / 3 : Real) <=
          (N : Real) ^ (4 / 3 : Real) / 2 := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN _) (by norm_num) htwo
      exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private lemma interval_fourier_four_thirds_mass {N M : Nat} [NeZero N]
    (b : ZMod N) (hMN : M <= N) :
    (∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real)) <=
      4 * (N : Real) ^ (4 / 3 : Real) := by
  calc
    (∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real)) <=
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
          (((N : Real) ^ (4 / 3 : Real) / 2) *
            (centeredAbs r : Real) ^ (-(4 / 3 : Real))) := by
      apply Finset.sum_le_sum
      intro r hr
      exact interval_decay_rpow_bound b r hMN
        (bne_iff_ne.mpr (Finset.mem_erase.mp hr).1)
    _ = ((N : Real) ^ (4 / 3 : Real) / 2) *
        ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
          (centeredAbs r : Real) ^ (-(4 / 3 : Real)) := by
      rw [Finset.mul_sum]
    _ <= ((N : Real) ^ (4 / 3 : Real) / 2) * 8 := by
      exact mul_le_mul_of_nonneg_left sum_centeredAbs_inv_four_thirds_le_eight
        (div_nonneg (Real.rpow_nonneg (by positivity) _) (by norm_num))
    _ = 4 * (N : Real) ^ (4 / 3 : Real) := by ring

private lemma sum_balanced_mul_indicator {N : Nat} [NeZero N]
    (A P : Finset (ZMod N)) :
    ∑ x : ZMod N, balanced A x * star (indicator P x) =
      (((A ∩ P).card : Real) - density A * P.card : Real) := by
  classical
  calc
    ∑ x : ZMod N, balanced A x * star (indicator P x) =
        ∑ x : ZMod N, if x ∈ P then balanced A x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ P <;> simp [indicator, hx]
    _ = ∑ x ∈ P, balanced A x := by simp
    _ = (((A ∩ P).card : Real) - density A * P.card : Real) := by
      simp only [balanced, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [show ∑ x ∈ P, indicator A x = ((P ∩ A).card : Complex) by simp [indicator]]
      push_cast
      rw [Finset.inter_comm P A]
      ring

private lemma cubeDifference_one_interval {N : Nat} (f : ZMod N -> Complex)
    (a : Point N 1) : cubeDifference f a = difference f (a 0) := by
  funext s
  simp only [cubeDifference, List.ofFn_succ, List.ofFn_zero, iteratedDifference]

private lemma degreeOneEnergy_eq_correlation_interval {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) :
    ∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 =
      ∑ r : ZMod N, ‖∑ s : ZMod N, difference f r s‖ ^ 2 := by
  let e := Equiv.funUnique (Fin 1) (ZMod N)
  have h := e.sum_comp fun r : ZMod N =>
    ‖∑ s : ZMod N, difference f r s‖ ^ 2
  simpa [e, cubeDifference_one_interval] using h

private lemma fourthMoment_eq_degreeOneEnergy_interval {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) :
    ∑ r : ZMod N, ‖fourier f r‖ ^ 4 =
      (N : Real) * ∑ a : Point N 1,
        ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 := by
  have h := lemma_2_1_holds N f f
  rw [degreeOneEnergy_eq_correlation_interval]
  simpa only [difference, ← pow_add] using h

private lemma uniformSet_degree_one_fourthMoment {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (hU : UniformSetOfDegree A alpha 1) :
    ∑ r : ZMod N, ‖fourier (balanced A) r‖ ^ 4 <= alpha * (N : Real) ^ 4 := by
  have hN : (0 : Real) <= N := by positivity
  unfold UniformSetOfDegree UniformOfDegree at hU
  calc
    ∑ r : ZMod N, ‖fourier (balanced A) r‖ ^ 4 =
        (N : Real) * ∑ a : Point N 1,
          ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 :=
      fourthMoment_eq_degreeOneEnergy_interval _
    _ <= (N : Real) * (alpha * (N : Real) ^ (1 + 2)) :=
      mul_le_mul_of_nonneg_left hU hN
    _ = alpha * (N : Real) ^ 4 := by ring

private lemma alpha_nonneg_of_degree_one_uniform {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (hU : UniformSetOfDegree A alpha 1) :
    0 <= alpha := by
  have hfour := uniformSet_degree_one_fourthMoment A alpha hU
  have hnonneg : 0 <= alpha * (N : Real) ^ 4 :=
    (Finset.sum_nonneg fun r _ => pow_nonneg (norm_nonneg _) _).trans hfour
  exact nonneg_of_mul_nonneg_left hnonneg
    (pow_pos (by exact_mod_cast NeZero.pos N : (0 : Real) < N) 4)

private lemma uniform_fourthMoment_root_le {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (hU : UniformSetOfDegree A alpha 1) :
    ((∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      ‖fourier (balanced A) r‖ ^ 4 : Real) ^ (1 / 4 : Real)) <=
      alpha ^ (1 / 4 : Real) * N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have ha : 0 <= alpha := alpha_nonneg_of_degree_one_uniform A alpha hU
  have hsum_nonneg : 0 <= ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      ‖fourier (balanced A) r‖ ^ 4 :=
    Finset.sum_nonneg fun r _ => pow_nonneg (norm_nonneg _) _
  have herase :
      (∑ r ∈ (Finset.univ.erase (0 : ZMod N)), ‖fourier (balanced A) r‖ ^ 4) <=
        ∑ r : ZMod N, ‖fourier (balanced A) r‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun _ _ _ => pow_nonneg (norm_nonneg _) _)
  calc
    ((∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖fourier (balanced A) r‖ ^ 4 : Real) ^ (1 / 4 : Real)) <=
        (alpha * (N : Real) ^ 4) ^ (1 / 4 : Real) := by
      apply Real.rpow_le_rpow hsum_nonneg
      · exact herase.trans (uniformSet_degree_one_fourthMoment A alpha hU)
      · norm_num
    _ = alpha ^ (1 / 4 : Real) * N := by
      rw [Real.mul_rpow ha (pow_nonneg hN.le 4)]
      congr 1
      convert Real.pow_rpow_inv_natCast hN.le (by norm_num : (4 : Nat) ≠ 0) using 1
      all_goals norm_num

private lemma four_rpow_three_fourths_le_three :
    (4 : Real) ^ (3 / 4 : Real) <= 3 := by
  refine le_of_pow_le_pow_left₀ (by norm_num : (4 : Nat) ≠ 0) (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) <= 4)]
  norm_num

private lemma interval_fourier_four_thirds_root {N M : Nat} [NeZero N]
    (b : ZMod N) (hMN : M <= N) :
    ((∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real)) ^
        (3 / 4 : Real)) <= 3 * N := by
  have hN : (0 : Real) <= N := by positivity
  have hsum_nonneg : 0 <= ∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
      ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real) :=
    Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _
  calc
    ((∑ r ∈ (Finset.univ.erase (0 : ZMod N)),
        ‖fourier (indicator (modInterval N b M).carrier) r‖ ^ (4 / 3 : Real)) ^
          (3 / 4 : Real)) <=
        (4 * (N : Real) ^ (4 / 3 : Real)) ^ (3 / 4 : Real) := by
      exact Real.rpow_le_rpow hsum_nonneg (interval_fourier_four_thirds_mass b hMN) (by norm_num)
    _ = (4 : Real) ^ (3 / 4 : Real) * N := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN _), ← Real.rpow_mul hN]
      norm_num
    _ <= 3 * N := mul_le_mul_of_nonneg_right four_rpow_three_fourths_le_three hN

@[simp] private lemma fourier_balanced_zero_interval {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : fourier (balanced A) 0 = 0 := by
  simp [fourier, ZMod.dft_apply]

/-- Gowers's Lemma 3.5, with the interval-length and Fourier-constant repairs
recorded in the statement catalogue. -/
theorem lemma_3_5_holds : lemma_3_5 := by
  intro N _ A alpha delta beta a M hcard hU hMN hM
  classical
  let P : Finset (ZMod N) := (modInterval N (a + 1) M).carrier
  let f : ZMod N -> Complex := balanced A
  let g : ZMod N -> Complex := indicator P
  let S : Finset (ZMod N) := Finset.univ.erase 0
  let term : ZMod N -> Complex := fun r => fourier f r * star (fourier g r)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hPcard : P.card = M := by
    exact modInterval_card (a + 1) hMN
  have hdensity : density A = delta := by
    rw [density, hcard]
    field_simp [show (N : Real) ≠ 0 by positivity]
  have hspace :
      ∑ x : ZMod N, f x * star (g x) =
        ((((A ∩ P).card : Real) - beta * delta * N : Real) : Complex) := by
    dsimp only [f, g]
    rw [sum_balanced_mul_indicator, hdensity, hPcard]
    have hMC : (M : Complex) = (beta : Complex) * (N : Complex) := by
      exact_mod_cast hM
    push_cast
    rw [hMC]
    ring
  have hfreq :
      ∑ r ∈ S, term r = (N : Complex) * ∑ x : ZMod N, f x * star (g x) := by
    calc
      ∑ r ∈ S, term r = ∑ r : ZMod N, term r := by
        dsimp only [S]
        rw [← Finset.sum_erase_add Finset.univ term
          (Finset.mem_univ (0 : ZMod N))]
        simp [term, f]
      _ = (N : Complex) * ∑ x : ZMod N, f x * star (g x) :=
        identity_2_2_holds N f g
  have hnorm_identity :
      ‖∑ r ∈ S, term r‖ =
        (N : Real) * |((A ∩ P).card : Real) - beta * delta * N| := by
    rw [hfreq, hspace, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
  have hpq : Real.HolderConjugate (4 : Real) (4 / 3 : Real) := by
    refine ⟨?_, by norm_num, by norm_num⟩
    norm_num [div_eq_mul_inv]
  have hholder :
      (∑ r ∈ S, ‖fourier f r‖ * ‖fourier g r‖) <=
        ((∑ r ∈ S, ‖fourier f r‖ ^ 4 : Real) ^ (1 / 4 : Real)) *
          ((∑ r ∈ S, ‖fourier g r‖ ^ (4 / 3 : Real)) ^ (3 / 4 : Real)) := by
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := S) (f := fun r => ‖fourier f r‖) (g := fun r => ‖fourier g r‖) hpq
      (fun r _ => norm_nonneg _) (fun r _ => norm_nonneg _)
    have hpow :
        (∑ r ∈ S, ‖fourier f r‖ ^ (4 : Real)) =
          ∑ r ∈ S, ‖fourier f r‖ ^ 4 := by
      apply Finset.sum_congr rfl
      intro r _
      exact Real.rpow_natCast _ 4
    have hqinv : (1 / (4 / 3 : Real)) = 3 / 4 := by norm_num
    rw [hpow, hqinv] at h
    exact h
  have hfroot :
      ((∑ r ∈ S, ‖fourier f r‖ ^ 4 : Real) ^ (1 / 4 : Real)) <=
        alpha ^ (1 / 4 : Real) * N := by
    simpa only [S, f] using uniform_fourthMoment_root_le A alpha hU
  have hgroot :
      ((∑ r ∈ S, ‖fourier g r‖ ^ (4 / 3 : Real)) ^ (3 / 4 : Real)) <=
        3 * N := by
    simpa only [S, g, P] using
      interval_fourier_four_thirds_root (N := N) (M := M) (a + 1) hMN
  have haroot : 0 <= alpha ^ (1 / 4 : Real) :=
    Real.rpow_nonneg (alpha_nonneg_of_degree_one_uniform A alpha hU) _
  refine le_of_mul_le_mul_left ?_ hN
  rw [← hnorm_identity]
  calc
    ‖∑ r ∈ S, term r‖ <= ∑ r ∈ S, ‖term r‖ := norm_sum_le _ _
    _ = ∑ r ∈ S, ‖fourier f r‖ * ‖fourier g r‖ := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [term, norm_mul, norm_star]
    _ <= ((∑ r ∈ S, ‖fourier f r‖ ^ 4 : Real) ^ (1 / 4 : Real)) *
        ((∑ r ∈ S, ‖fourier g r‖ ^ (4 / 3 : Real)) ^ (3 / 4 : Real)) := hholder
    _ <= (alpha ^ (1 / 4 : Real) * N) * (3 * N) := by
      exact mul_le_mul hfroot hgroot
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun r _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg haroot hN.le)
    _ = (N : Real) * (3 * alpha ^ (1 / 4 : Real) * N) := by ring

end LeanProofs.GowersSzemeredi
