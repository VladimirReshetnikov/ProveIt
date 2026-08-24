import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Analysis.MeanInequalities

/-!
# Proofs for Gowers (2001), Lemma 2.2

The five uniformity conditions are connected by the exact Fourier identities
proved in `Proofs01_03` and elementary finite-sum inequalities.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma fourthMoment_eq_correlationEnergy {N : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    ∑ r : ZMod N, ‖fourier f r‖ ^ 4 =
      (N : Real) * ∑ t : ZMod N,
        ‖∑ s : ZMod N, f s * star (f (s - t))‖ ^ 2 := by
  have h := lemma_2_1_holds N f f
  convert h using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma fourthMoment_eq_quadrupleSum {N : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    ∑ r : ZMod N, ‖fourier f r‖ ^ 4 =
      (N : Real) *
        (∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3
            then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
            else 0).re := by
  have h := congrArg Complex.re (identity_2_6_holds N f)
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, Nat.cast_ofNat, zero_mul, mul_zero,
    sub_zero] using h

private lemma condition_i_iff_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c : Real) :
    uniformCondition2i f c ↔ uniformCondition2iii f c := by
  let E := ∑ t : ZMod N,
    ‖∑ s : ZMod N, f s * star (f (s - t))‖ ^ 2
  let F := ∑ r : ZMod N, ‖fourier f r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hFE : F = (N : Real) * E := fourthMoment_eq_correlationEnergy f
  change E ≤ c * (N : Real) ^ 3 ↔ F ≤ c * (N : Real) ^ 4
  constructor
  · intro h
    calc
      F = (N : Real) * E := hFE
      _ ≤ (N : Real) * (c * (N : Real) ^ 3) :=
        mul_le_mul_of_nonneg_left h hN.le
      _ = c * (N : Real) ^ 4 := by ring
  · intro h
    refine le_of_mul_le_mul_left ?_ hN
    calc
      (N : Real) * E = F := hFE.symm
      _ ≤ c * (N : Real) ^ 4 := h
      _ = (N : Real) * (c * (N : Real) ^ 3) := by ring

private lemma condition_ii_iff_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c : Real) :
    uniformCondition2ii f c ↔ uniformCondition2iii f c := by
  let Q := (∑ q : Fin 4 → ZMod N,
    if q 0 - q 1 = q 2 - q 3
      then f (q 0) * star (f (q 1) * f (q 2)) * f (q 3)
      else 0).re
  let F := ∑ r : ZMod N, ‖fourier f r‖ ^ 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hFQ : F = (N : Real) * Q := fourthMoment_eq_quadrupleSum f
  change Q ≤ c * (N : Real) ^ 3 ↔ F ≤ c * (N : Real) ^ 4
  constructor
  · intro h
    calc
      F = (N : Real) * Q := hFQ
      _ ≤ (N : Real) * (c * (N : Real) ^ 3) :=
        mul_le_mul_of_nonneg_left h hN.le
      _ = c * (N : Real) ^ 4 := by ring
  · intro h
    refine le_of_mul_le_mul_left ?_ hN
    calc
      (N : Real) * Q = F := hFQ.symm
      _ ≤ c * (N : Real) ^ 4 := h
      _ = (N : Real) * (c * (N : Real) ^ 3) := by ring

private lemma condition_i_iff_ii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c : Real) :
    uniformCondition2i f c ↔ uniformCondition2ii f c :=
  (condition_i_iff_iii f c).trans (condition_ii_iff_iii f c).symm

private lemma condition_iii_imp_iv {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c1 c2 : Real)
    (hroot : c1 ^ ((1 : Real) / 4) ≤ c2)
    (hiii : uniformCondition2iii f c1) : uniformCondition2iv f c2 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsum_nonneg :
      0 ≤ ∑ q : ZMod N, ‖fourier f q‖ ^ 4 :=
    Finset.sum_nonneg fun q _ => pow_nonneg (norm_nonneg _) _
  have hc1mul : 0 ≤ c1 * (N : Real) ^ 4 := hsum_nonneg.trans hiii
  have hc1 : 0 ≤ c1 :=
    nonneg_of_mul_nonneg_left hc1mul (pow_pos hN 4)
  have hroot_nonneg : 0 ≤ c1 ^ ((1 : Real) / 4) :=
    Real.rpow_nonneg hc1 _
  have hroot_pow : (c1 ^ ((1 : Real) / 4)) ^ 4 = c1 := by
    convert Real.rpow_inv_natCast_pow hc1 (by norm_num : (4 : Nat) ≠ 0) using 1
    all_goals norm_num
  intro r
  have hr_sum : ‖fourier f r‖ ^ 4 ≤
      ∑ q : ZMod N, ‖fourier f q‖ ^ 4 := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (ZMod N)))
        (f := fun q => ‖fourier f q‖ ^ 4)
        (fun q _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ r))
  have hr_pow : ‖fourier f r‖ ^ 4 ≤
      (c1 ^ ((1 : Real) / 4) * (N : Real)) ^ 4 := by
    calc
      ‖fourier f r‖ ^ 4 ≤ ∑ q : ZMod N, ‖fourier f q‖ ^ 4 := hr_sum
      _ ≤ c1 * (N : Real) ^ 4 := hiii
      _ = (c1 ^ ((1 : Real) / 4) * (N : Real)) ^ 4 := by
        rw [mul_pow, hroot_pow]
  have hr : ‖fourier f r‖ ≤ c1 ^ ((1 : Real) / 4) * (N : Real) :=
    le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg hroot_nonneg hN.le) hr_pow
  exact hr.trans (mul_le_mul_of_nonneg_right hroot hN.le)

private lemma condition_iv_imp_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (hdisc : DiscValued f) (c1 c2 : Real)
    (hsq : c2 ^ 2 ≤ c1) (hiv : uniformCondition2iv f c2) :
    uniformCondition2iii f c1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hparseval :
      ∑ r : ZMod N, ‖fourier f r‖ ^ 2 ≤ (N : Real) ^ 2 := by
    calc
      ∑ r : ZMod N, ‖fourier f r‖ ^ 2 =
          (N : Real) * ∑ s : ZMod N, ‖f s‖ ^ 2 := identity_2_3_holds N f
      _ ≤ (N : Real) * ∑ _s : ZMod N, (1 : Real) := by
        apply mul_le_mul_of_nonneg_left _ hN.le
        apply Finset.sum_le_sum
        intro s _
        exact pow_le_one₀ (norm_nonneg _) (hdisc s)
      _ = (N : Real) ^ 2 := by simp [ZMod.card]; ring
  calc
    ∑ r : ZMod N, ‖fourier f r‖ ^ 4 ≤
        ∑ r : ZMod N, (c2 * (N : Real)) ^ 2 * ‖fourier f r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      calc
        ‖fourier f r‖ ^ 4 = ‖fourier f r‖ ^ 2 * ‖fourier f r‖ ^ 2 := by ring
        _ ≤ (c2 * (N : Real)) ^ 2 * ‖fourier f r‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hiv r) 2) (sq_nonneg _)
    _ = (c2 * (N : Real)) ^ 2 *
        ∑ r : ZMod N, ‖fourier f r‖ ^ 2 := by rw [mul_sum]
    _ ≤ (c2 * (N : Real)) ^ 2 * (N : Real) ^ 2 :=
      mul_le_mul_of_nonneg_left hparseval (sq_nonneg _)
    _ = c2 ^ 2 * (N : Real) ^ 4 := by ring
    _ ≤ c1 * (N : Real) ^ 4 :=
      mul_le_mul_of_nonneg_right hsq (pow_nonneg hN.le _)

private lemma condition_v_imp_i {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (hdisc : DiscValued f) (c1 c3 : Real)
    (hc : c3 ≤ c1) (hv : uniformCondition2v f c3) :
    uniformCondition2i f c1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hc3mul : 0 ≤ c3 * (N : Real) ^ 3 := by
    calc
      0 ≤ ∑ k : ZMod N,
          ‖∑ s : ZMod N, f s * star ((1 : ZMod N → Complex) (s - k))‖ ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      _ ≤ c3 * (N : Real) ^ 2 *
          ∑ s : ZMod N, ‖(1 : ZMod N → Complex) s‖ ^ 2 := hv 1
      _ = c3 * (N : Real) ^ 3 := by simp [ZMod.card]; ring
  have hc3 : 0 ≤ c3 :=
    nonneg_of_mul_nonneg_left hc3mul (pow_pos hN 3)
  have hfnorm : ∑ s : ZMod N, ‖f s‖ ^ 2 ≤ (N : Real) := by
    calc
      ∑ s : ZMod N, ‖f s‖ ^ 2 ≤ ∑ _s : ZMod N, (1 : Real) := by
        apply Finset.sum_le_sum
        intro s _
        exact pow_le_one₀ (norm_nonneg _) (hdisc s)
      _ = (N : Real) := by simp [ZMod.card]
  calc
    ∑ k : ZMod N, ‖∑ s : ZMod N, f s * star (f (s - k))‖ ^ 2 ≤
        c3 * (N : Real) ^ 2 * ∑ s : ZMod N, ‖f s‖ ^ 2 := hv f
    _ ≤ c3 * (N : Real) ^ 2 * (N : Real) :=
      mul_le_mul_of_nonneg_left hfnorm (mul_nonneg hc3 (sq_nonneg _))
    _ = c3 * (N : Real) ^ 3 := by ring
    _ ≤ c1 * (N : Real) ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hN.le _)

private lemma condition_iii_imp_v {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c1 c3 : Real)
    (hroot : c1 ^ ((1 : Real) / 2) ≤ c3)
    (hiii : uniformCondition2iii f c1) : uniformCondition2v f c3 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hF4_nonneg : 0 ≤ ∑ r : ZMod N, ‖fourier f r‖ ^ 4 :=
    Finset.sum_nonneg fun r _ => pow_nonneg (norm_nonneg _) _
  have hc1mul : 0 ≤ c1 * (N : Real) ^ 4 := hF4_nonneg.trans hiii
  have hc1 : 0 ≤ c1 :=
    nonneg_of_mul_nonneg_left hc1mul (pow_pos hN 4)
  have hroot_nonneg : 0 ≤ c1 ^ ((1 : Real) / 2) :=
    Real.rpow_nonneg hc1 _
  intro g
  let F4 := ∑ r : ZMod N, ‖fourier f r‖ ^ 4
  let G4 := ∑ r : ZMod N, ‖fourier g r‖ ^ 4
  let G2 := ∑ r : ZMod N, ‖fourier g r‖ ^ 2
  let S := ∑ r : ZMod N, ‖fourier f r‖ ^ 2 * ‖fourier g r‖ ^ 2
  let E := ∑ k : ZMod N,
    ‖∑ s : ZMod N, f s * star (g (s - k))‖ ^ 2
  have hSE : S = (N : Real) * E := lemma_2_1_holds N f g
  have hCS : S ≤ Real.sqrt F4 * Real.sqrt G4 := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (ZMod N))
      (fun r => ‖fourier f r‖ ^ 2) (fun r => ‖fourier g r‖ ^ 2)
    simpa [S, F4, G4, ← pow_mul] using h
  have hsqrtF : Real.sqrt F4 ≤
      c1 ^ ((1 : Real) / 2) * (N : Real) ^ 2 := by
    calc
      Real.sqrt F4 ≤ Real.sqrt (c1 * (N : Real) ^ 4) :=
        Real.sqrt_le_sqrt hiii
      _ = Real.sqrt c1 * Real.sqrt ((N : Real) ^ 4) :=
        Real.sqrt_mul hc1 _
      _ = c1 ^ ((1 : Real) / 2) * (N : Real) ^ 2 := by
        rw [Real.sqrt_eq_rpow]
        rw [show (N : Real) ^ 4 = ((N : Real) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (sq_nonneg _)]
  have hG2_nonneg : 0 ≤ G2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  have hsqrtG : Real.sqrt G4 ≤ G2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hG2_nonneg, ?_⟩
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset (ZMod N)))
      (f := fun r => ‖fourier g r‖ ^ 2)
      (fun r _ => sq_nonneg _)
    simpa [G4, G2, ← pow_mul] using h
  have hparseval : G2 = (N : Real) * ∑ s : ZMod N, ‖g s‖ ^ 2 :=
    identity_2_3_holds N g
  refine le_of_mul_le_mul_left ?_ hN
  calc
    (N : Real) * E = S := hSE.symm
    _ ≤ Real.sqrt F4 * Real.sqrt G4 := hCS
    _ ≤ (c1 ^ ((1 : Real) / 2) * (N : Real) ^ 2) * G2 := by
      exact mul_le_mul hsqrtF hsqrtG (Real.sqrt_nonneg _)
        (mul_nonneg hroot_nonneg (sq_nonneg _))
    _ ≤ (c3 * (N : Real) ^ 2) * G2 := by
      apply mul_le_mul_of_nonneg_right _ hG2_nonneg
      exact mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
    _ = (N : Real) *
        (c3 * (N : Real) ^ 2 * ∑ s : ZMod N, ‖g s‖ ^ 2) := by
      rw [hparseval]
      ring

/-- **Gowers, Lemma 2.2.** The five formulations of Fourier uniformity,
with the quantitative power losses recorded in the paper. -/
theorem lemma_2_2_holds : lemma_2_2 := by
  intro N _ f hdisc c1 c2 c3
  refine ⟨condition_i_iff_ii f c1, condition_i_iff_iii f c1, ?_, ?_, ?_, ?_⟩
  · exact fun h hiii => condition_iii_imp_iv f c1 c2 h hiii
  · exact fun h hiv => condition_iv_imp_iii f hdisc c1 c2 h hiv
  · exact fun h hv => condition_v_imp_i f hdisc c1 c3 h hv
  · exact fun h hiii => condition_iii_imp_v f c1 c3 h hiii

end LeanProofs.GowersSzemeredi
