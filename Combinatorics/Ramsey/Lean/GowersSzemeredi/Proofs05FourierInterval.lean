import GowersSzemeredi.Section05
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GowersSzemeredi.Proofs00Basics

/-!
# Fourier decay of a centered interval

This module proves Lemma 5.1.  The interval is first identified with its
integer representatives in `[-M,M)`, after which its Fourier transform is a
finite geometric progression.  Jordan's inequality supplies the stated
low-frequency denominator.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma centeredInterval_cast_injective (N M : Nat) [NeZero N]
    (hMN : 2 * M <= N) :
    Set.InjOn (fun x : Int => (x : ZMod N)) (Finset.Ico (-(M : Int)) (M : Int)) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_Ico] at hx hy
  have hdvd : (N : Int) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y N).mp hxy
  have habs : |y - x| < (N : Int) := by
    have hlower : -(2 * (M : Int)) < y - x := by linarith
    have hupper : y - x < 2 * (M : Int) := by linarith
    have hMN' : (2 * (M : Int)) <= N := by exact_mod_cast hMN
    rw [abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg hMN') hlower, hupper.trans_le hMN'⟩
  have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

private lemma centeredInterval_card (N M : Nat) [NeZero N]
    (hMN : 2 * M <= N) :
    (centeredInterval N M).card = 2 * M := by
  rw [centeredInterval, Finset.card_image_iff.mpr]
  · simp only [Int.card_Ico, sub_neg_eq_add]
    rw [Int.toNat_add (by positivity) (by positivity)]
    simp
    omega
  · exact centeredInterval_cast_injective N M hMN

private lemma fourier_centeredInterval_eq_int_sum (N M : Nat) [NeZero N]
    (hMN : 2 * M <= N) (r : ZMod N) :
    fourier (indicator (centeredInterval N M)) r =
      ∑ x ∈ Finset.Ico (-(M : Int)) (M : Int),
        ZMod.stdAddChar (-((x : ZMod N) * r)) := by
  rw [fourier, ZMod.dft_apply]
  simp only [indicator, smul_eq_mul]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  simp only [Finset.filter_univ_mem]
  rw [centeredInterval]
  exact Finset.sum_image
    (f := fun j : ZMod N => ZMod.stdAddChar (-(j * r)))
    (g := fun x : Int => (x : ZMod N))
    (centeredInterval_cast_injective N M hMN)

private lemma centered_character_eq_zpow {N : Nat} [NeZero N]
    (r : ZMod N) (x : Int) :
    ZMod.stdAddChar (-((x : ZMod N) * r)) = (ZMod.stdAddChar (-r)) ^ x := by
  rw [← AddChar.map_zsmul_eq_zpow]
  congr 1
  simp only [zsmul_eq_mul]
  ring

private lemma int_Ico_zpow_sum_eq (M : Nat) (q : Complex) (hq : q ≠ 0) :
    (∑ x ∈ Finset.Ico (-(M : Int)) (M : Int), q ^ x) =
      q ^ (-(M : Int)) * ∑ i ∈ Finset.range (2 * M), q ^ i := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  have hlen : ((M : Int) - -(M : Int)).toNat = 2 * M := by omega
  rw [hlen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change q ^ (-(M : Int) + (i : Int)) = q ^ (-(M : Int)) * q ^ i
  rw [zpow_add₀ hq, zpow_natCast]

private lemma norm_centered_character_sum_le {N : Nat} [NeZero N]
    (M : Nat) (r : ZMod N) (hr : r ≠ 0) :
    ‖∑ x ∈ Finset.Ico (-(M : Int)) (M : Int),
        ZMod.stdAddChar (-((x : ZMod N) * r))‖ <=
      2 / ‖ZMod.stdAddChar (-r) - 1‖ := by
  let q : Complex := ZMod.stdAddChar (-r)
  have hq0 : q ≠ 0 := by
    rw [← norm_ne_zero_iff]
    exact (AddChar.norm_apply (ZMod.stdAddChar (N := N)) (-r)).trans_ne one_ne_zero
  have hq1 : q ≠ 1 := by
    intro h
    have hneg : -r = 0 := ZMod.injective_stdAddChar (by
      simpa [q] using h)
    exact hr (neg_eq_zero.mp hneg)
  simp_rw [centered_character_eq_zpow]
  rw [int_Ico_zpow_sum_eq M q hq0, norm_mul, Complex.norm_zpow,
    AddChar.norm_apply, one_zpow, one_mul, geom_sum_eq hq1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖q ^ (2 * M) - 1‖ <= ‖q ^ (2 * M)‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, AddChar.norm_apply]; norm_num

private lemma stdAddChar_neg_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (r : ZMod N) :
    ZMod.stdAddChar (-r) =
      Complex.exp (Complex.I * (-(2 * Real.pi * (r.valMinAbs : Real) / N) : Real)) := by
  calc
    ZMod.stdAddChar (-r) = ZMod.stdAddChar ((-r.valMinAbs : Int) : ZMod N) := by norm_num
    _ = Complex.exp (2 * Real.pi * Complex.I * (-r.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe (-r.valMinAbs)
    _ = Complex.exp (Complex.I *
        (-(2 * Real.pi * (r.valMinAbs : Real) / N) : Real)) := by push_cast; ring

/-- Jordan's inequality gives a uniform lower bound for the denominator in a
finite geometric character sum. -/
lemma character_denominator_lower_bound {N : Nat} [NeZero N]
    (r : ZMod N) :
    4 * (centeredAbs r : Real) / N <= ‖ZMod.stdAddChar (-r) - 1‖ := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have h2 : 2 * (centeredAbs r : Real) ≤ N := by
    have := ZMod.natAbs_valMinAbs_le r
    exact_mod_cast (show 2 * centeredAbs r ≤ N by unfold centeredAbs; omega)
  have hx : |Real.pi * r.valMinAbs / N| = Real.pi * centeredAbs r / N := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN, centeredAbs, Nat.cast_natAbs,
      Int.cast_abs]
  -- Jordan's inequality at `π r / N`, which lies in `[-π/2, π/2]`
  have hj := Real.mul_abs_le_abs_sin (x := Real.pi * r.valMinAbs / N) (by
    rw [hx, div_le_div_iff₀ hN two_pos]; nlinarith [Real.pi_pos])
  rw [hx] at hj
  rw [stdAddChar_neg_eq_exp_valMinAbs, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_two, show -(2 * Real.pi * (r.valMinAbs : Real) / N) / 2 =
      -(Real.pi * r.valMinAbs / N) by ring, Real.sin_neg, abs_neg]
  calc 4 * (centeredAbs r : Real) / N = 2 * (2 / Real.pi * (Real.pi * centeredAbs r / N)) := by
        field_simp; ring
    _ ≤ _ := by gcongr

/-- Lemma 5.1: Fourier decay of a centered interval. -/
theorem lemma_5_1_holds : lemma_5_1 := by
  intro N M _ hMN r
  refine ⟨(fourier_indicator_norm_le_card _ r).trans_eq (by simp [centeredInterval_card N M hMN]),
    fun hr => ?_⟩
  have hr' : r ≠ 0 := bne_iff_ne.mp hr
  have habs : (0 : Real) < centeredAbs r := by simpa [centeredAbs] using hr'
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlower := (div_le_iff₀ hN).mp (character_denominator_lower_bound r)
  rw [fourier_centeredInterval_eq_int_sum N M hMN r]
  refine (norm_centered_character_sum_le M r hr').trans
    ((div_le_div_iff₀ (by nlinarith) (by linarith)).2 ?_)
  linarith

end LeanProofs.GowersSzemeredi
