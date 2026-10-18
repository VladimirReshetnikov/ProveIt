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

/-- An identity `F = N X` with `N > 0` turns the bound `X ≤ c N³` into `F ≤ c N⁴`. -/
private lemma le_cube_iff_le_fourth {N X F c : Real} (hN : 0 < N) (h : F = N * X) :
    X ≤ c * N ^ 3 ↔ F ≤ c * N ^ 4 := by
  rw [h, show c * N ^ 4 = N * (c * N ^ 3) by ring, mul_le_mul_iff_right₀ hN]

private lemma condition_i_iff_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c : Real) :
    uniformCondition2i f c ↔ uniformCondition2iii f c := by
  refine le_cube_iff_le_fourth (by exact_mod_cast NeZero.pos N) ?_
  convert lemma_2_1_holds N f f using 1
  exact Finset.sum_congr rfl fun r _ => by ring

private lemma condition_ii_iff_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c : Real) :
    uniformCondition2ii f c ↔ uniformCondition2iii f c := by
  refine le_cube_iff_le_fourth (by exact_mod_cast NeZero.pos N) ?_
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, Nat.cast_ofNat, zero_mul, mul_zero,
    sub_zero] using congrArg Complex.re (identity_2_6_holds N f)

private lemma condition_iii_imp_iv {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c1 c2 : Real)
    (hroot : c1 ^ ((1 : Real) / 4) ≤ c2)
    (hiii : uniformCondition2iii f c1) : uniformCondition2iv f c2 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  intro r
  have hr : ‖fourier f r‖ ^ 4 ≤ c1 * (N : Real) ^ 4 :=
    (single_le_sum (fun q _ => pow_nonneg (norm_nonneg (fourier f q)) 4) (mem_univ r)).trans hiii
  have hc1 : 0 ≤ c1 :=
    nonneg_of_mul_nonneg_left ((pow_nonneg (norm_nonneg _) 4).trans hr) (by positivity)
  have h4 : (c1 ^ ((1 : Real) / 4)) ^ 4 = c1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc1]
    norm_num
  -- take fourth roots: `‖f̂ r‖ ≤ c1 ^ (1/4) * N ≤ c2 * N`
  refine le_trans (le_of_pow_le_pow_left₀ four_ne_zero (by positivity) ?_)
    (mul_le_mul_of_nonneg_right hroot hN.le)
  rwa [mul_pow, h4]

private lemma condition_iv_imp_iii {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (hdisc : DiscValued f) (c1 c2 : Real)
    (hsq : c2 ^ 2 ≤ c1) (hiv : uniformCondition2iv f c2) :
    uniformCondition2iii f c1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- Parseval with `‖f‖ ≤ 1`: `∑ ‖f̂‖² = N ∑ ‖f‖² ≤ N²`
  have hparseval : ∑ r : ZMod N, ‖fourier f r‖ ^ 2 ≤ (N : Real) ^ 2 := by
    rw [identity_2_3_holds N f, sq]
    exact mul_le_mul_of_nonneg_left ((sum_le_sum fun s _ =>
      pow_le_one₀ (norm_nonneg _) (hdisc s)).trans_eq (by simp [ZMod.card])) hN.le
  calc ∑ r, ‖fourier f r‖ ^ 4 ≤ ∑ r, (c2 * N) ^ 2 * ‖fourier f r‖ ^ 2 :=
        sum_le_sum fun r _ => by
          rw [show ‖fourier f r‖ ^ 4 = ‖fourier f r‖ ^ 2 * ‖fourier f r‖ ^ 2 by ring]
          gcongr
          exact hiv r
    _ ≤ c2 ^ 2 * N ^ 4 := by
        rw [← mul_sum]
        nlinarith [mul_le_mul_of_nonneg_left hparseval (sq_nonneg (c2 * N))]
    _ ≤ c1 * N ^ 4 := by gcongr

private lemma condition_v_imp_i {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (hdisc : DiscValued f) (c1 c3 : Real)
    (hc : c3 ≤ c1) (hv : uniformCondition2v f c3) :
    uniformCondition2i f c1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hone : ∑ _s : ZMod N, (1 : Real) = N := by simp [ZMod.card]
  -- testing (v) against `g = 1` shows `c3 ≥ 0`
  have hc3 : 0 ≤ c3 := by
    have h := (hv 1).trans' (sum_nonneg fun k _ => sq_nonneg _)
    simp only [Pi.one_apply, norm_one, one_pow, hone] at h
    nlinarith [mul_pos (pow_pos hN 2) hN]
  calc ∑ k, ‖∑ s, f s * star (f (s - k))‖ ^ 2 ≤ c3 * N ^ 2 * ∑ s, ‖f s‖ ^ 2 := hv f
    _ ≤ c3 * N ^ 2 * N := by
        gcongr
        exact (sum_le_sum fun s _ => pow_le_one₀ (norm_nonneg _) (hdisc s)).trans_eq hone
    _ ≤ c1 * N ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg hN.le 3)]

private lemma condition_iii_imp_v {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (c1 c3 : Real)
    (hroot : c1 ^ ((1 : Real) / 2) ≤ c3)
    (hiii : uniformCondition2iii f c1) : uniformCondition2v f c3 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hc1 : 0 ≤ c1 := nonneg_of_mul_nonneg_left
    ((sum_nonneg fun r _ => pow_nonneg (norm_nonneg (fourier f r)) 4).trans hiii) (by positivity)
  rw [← Real.sqrt_eq_rpow] at hroot
  have hc3 : 0 ≤ c3 := (Real.sqrt_nonneg _).trans hroot
  have hc13 : c1 ≤ c3 ^ 2 := by
    nlinarith [Real.sq_sqrt hc1, mul_self_le_mul_self (Real.sqrt_nonneg c1) hroot]
  -- every coefficient has `‖f̂ r‖⁴ ≤ c1 * N⁴ ≤ (c3 * N²)²`, so `‖f̂ r‖² ≤ c3 * N²`
  have hcoef (r : ZMod N) : ‖fourier f r‖ ^ 2 ≤ c3 * (N : Real) ^ 2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc (‖fourier f r‖ ^ 2) ^ 2 = ‖fourier f r‖ ^ 4 := by ring
      _ ≤ c1 * N ^ 4 := (single_le_sum (fun q _ => pow_nonneg (norm_nonneg (fourier f q)) 4)
          (mem_univ r)).trans hiii
      _ ≤ (c3 * N ^ 2) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hc13 (pow_nonneg hN.le 4)]
  -- then Lemma 2.1 and Parseval: `N * E = ∑ ‖f̂‖² ‖ĝ‖² ≤ c3 N² ∑ ‖ĝ‖² = c3 N³ ∑ ‖g‖²`
  intro g
  refine le_of_mul_le_mul_left ?_ hN
  rw [← lemma_2_1_holds N f g]
  calc ∑ r, ‖fourier f r‖ ^ 2 * ‖fourier g r‖ ^ 2 ≤ ∑ r, c3 * N ^ 2 * ‖fourier g r‖ ^ 2 :=
        sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hcoef r) (sq_nonneg _)
    _ = N * (c3 * N ^ 2 * ∑ s, ‖g s‖ ^ 2) := by
        rw [← mul_sum, identity_2_3_holds N g]
        ring

/-- **Gowers, Lemma 2.2.** The five formulations of Fourier uniformity,
with the quantitative power losses recorded in the paper. -/
theorem lemma_2_2_holds : lemma_2_2 := by
  intro N _ f hdisc c1 c2 c3
  refine ⟨(condition_i_iff_iii f c1).trans (condition_ii_iff_iii f c1).symm, condition_i_iff_iii f c1, ?_, ?_, ?_, ?_⟩
  · exact fun h hiii => condition_iii_imp_iv f c1 c2 h hiii
  · exact fun h hiv => condition_iv_imp_iii f hdisc c1 c2 h hiv
  · exact fun h hv => condition_v_imp_i f hdisc c1 c3 h hv
  · exact fun h hiii => condition_iii_imp_v f c1 c3 h hiii

end LeanProofs.GowersSzemeredi
