import GowersSzemeredi.Section10
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Auxiliary parameters for Theorem 10.13

This module proves the three parameter facts needed to apply Corollary 10.11
with the actual large spectrum in Theorem 10.13: that the spectrum is
nonempty, that its Bohr radius lies in `(0, 1]`, and that the radius defined
using the ceiling spectrum parameter is small enough for the actual spectrum
cardinality.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma theorem1013Parameters_sum_fibre_cards {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) :
    (∑ s : ZMod N, (D.fibre s).card) = Fintype.card X := by
  rw [Fintype.card]
  exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
    (t := Finset.univ) (f := D.index) (by simp)).symm

@[simp] private lemma theorem1013Parameters_fourier_zero {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) :
    fourier (domainFibreCountFunction D) 0 = (Fintype.card X : Complex) := by
  rw [fourier, ZMod.dft_apply]
  simp [domainFibreCountFunction, ← Nat.cast_sum,
    theorem1013Parameters_sum_fibre_cards]

private lemma theorem1013Parameters_lambda_le_alpha (alpha : Real)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) :
    section10Lambda alpha ≤ alpha := by
  have htwo : (2 : Real) ^ (-(37 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have halphaPow : alpha ^ ((11 : Real) / 2) ≤ alpha := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge halpha halphaOne
        (by norm_num : (1 : Real) ≤ 11 / 2)
  unfold section10Lambda
  calc
    (2 : Real) ^ (-(37 : Real)) * alpha ^ ((11 : Real) / 2) ≤
        1 * alpha ^ ((11 : Real) / 2) := by
      gcongr
    _ ≤ alpha := by simpa using halphaPow

/-- The zero frequency belongs to the large spectrum in Theorem 10.13. -/
theorem theorem10_13_largeSpectrum_nonempty {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    (domainLargeSpectrum D (section10Lambda alpha * M * N)).Nonempty := by
  have halphaOne : alpha ≤ 1 := by linarith
  have hlambda := theorem1013Parameters_lambda_le_alpha alpha halpha halphaOne
  refine ⟨0, ?_⟩
  rw [domainLargeSpectrum, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [theorem1013Parameters_fourier_zero]
  calc
    section10Lambda alpha * (M : Real) * (N : Real) ≤
        alpha * (M : Real) * (N : Real) := by gcongr
    _ = (Fintype.card X : Real) := hcard.symm
    _ = ‖(Fintype.card X : Complex)‖ := by simp

lemma theorem1013Parameters_bohr_radius_eq (alpha : Real)
    (halpha : 0 < alpha) :
    section10BohrRadius alpha =
      (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by
  have htwo :
      ((2 : Real) ^ (-(37 : Real))) ^ (4 : Nat) =
        (2 : Real) ^ (-(148 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num)]
    norm_num
  have halphaFour :
      (alpha ^ ((11 : Real) / 2)) ^ (4 : Nat) = alpha ^ (22 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
    norm_num [Real.rpow_natCast]
  have halphaCombine :
      alpha ^ (-(4 : Real)) * alpha ^ (22 : Nat) = alpha ^ (18 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add halpha]
    norm_num [Real.rpow_natCast]
  unfold section10BohrRadius section10Lambda
  rw [mul_pow, htwo, halphaFour]
  calc
    alpha ^ (-(4 : Real)) *
          ((2 : Real) ^ (-(148 : Real)) * alpha ^ (22 : Nat)) / Real.pi =
        (2 : Real) ^ (-(148 : Real)) *
          (alpha ^ (-(4 : Real)) * alpha ^ (22 : Nat)) / Real.pi := by ring
    _ = (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by
      rw [halphaCombine]

/-- The Bohr radius `epsilon` in Theorem 10.13 is positive. -/
theorem theorem10_13_bohrRadius_pos (alpha : Real) (halpha : 0 < alpha) :
    0 < section10BohrRadius alpha := by
  unfold section10BohrRadius section10Lambda
  positivity

/-- In the parameter range of Theorem 10.13, its Bohr radius is at most one. -/
theorem theorem10_13_bohrRadius_le_one (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) :
    section10BohrRadius alpha ≤ 1 := by
  rw [theorem1013Parameters_bohr_radius_eq alpha halpha]
  have halphaOne : alpha ≤ 1 := by linarith
  have htwo : (2 : Real) ^ (-(148 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have halphaPow : alpha ^ (18 : Nat) ≤ 1 :=
    pow_le_one₀ halpha.le halphaOne
  have hnumerator :
      (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) ≤ 1 := by
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 2) (-(148 : Real)),
      pow_nonneg halpha.le (18 : Nat)]
  have hpiOne : (1 : Real) ≤ Real.pi := by linarith [Real.two_le_pi]
  exact (div_le_self (by positivity) hpiOne).trans hnumerator

lemma theorem1013Parameters_bohr_radius_lower (alpha : Real)
    (halpha : 0 < alpha) :
    (2 : Real) ^ (-(150 : Real)) * alpha ^ (18 : Nat) ≤
      section10BohrRadius alpha := by
  rw [theorem1013Parameters_bohr_radius_eq alpha halpha]
  have hpi : (0 : Real) < Real.pi := Real.pi_pos
  have hrecip : (1 : Real) / 4 ≤ 1 / Real.pi :=
    one_div_le_one_div_of_le hpi Real.pi_le_four
  have hcoeff :
      (2 : Real) ^ (-(150 : Real)) ≤
        (2 : Real) ^ (-(148 : Real)) / Real.pi := by
    calc
      (2 : Real) ^ (-(150 : Real)) =
          (2 : Real) ^ (-(148 : Real)) * (1 / 4) := by
        rw [show (1 / 4 : Real) = (2 : Real) ^ (-(2 : Real)) by
          norm_num [Real.rpow_neg, Real.rpow_two]]
        rw [← Real.rpow_add (show (0 : Real) < 2 by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (-(148 : Real)) * (1 / Real.pi) := by gcongr
      _ = (2 : Real) ^ (-(148 : Real)) / Real.pi := by ring
  calc
    (2 : Real) ^ (-(150 : Real)) * alpha ^ (18 : Nat) ≤
        ((2 : Real) ^ (-(148 : Real)) / Real.pi) *
          alpha ^ (18 : Nat) := by gcongr
    _ = (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by
      ring

/-- The corrected `zeta` is small enough at the ceiling spectrum parameter. -/
theorem theorem10_13_zeta_le_parameterRadius (alpha : Real)
    (halpha : 0 < alpha) :
    let k := section10SpectrumParameter alpha
    section10Zeta alpha ≤
      (2 : Real) ^ (-((k : Real) + 4)) * section10BohrRadius alpha ^ k / k := by
  intro k
  have hk : (1 : Real) ≤ k := by
    have : 0 < section10SpectrumBound alpha := by unfold section10SpectrumBound; positivity
    exact_mod_cast Nat.ceil_pos.mpr this
  -- `2 ^ (-155 k) ≤ 2 ^ (-(k + 4)) * (2 ^ (-150)) ^ k` because `k ≥ 1`
  have hcoeff : (2 : Real) ^ (-(155 : Real) * k) ≤
      (2 : Real) ^ (-((k : Real) + 4)) * ((2 : Real) ^ (-(150 : Real))) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num),
      ← Real.rpow_add (show (0 : Real) < 2 by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc section10Zeta alpha = (2 : Real) ^ (-(155 : Real) * k) * alpha ^ (18 * k) / k := rfl
    _ ≤ (2 : Real) ^ (-((k : Real) + 4)) *
        ((2 : Real) ^ (-(150 : Real)) * alpha ^ 18) ^ k / k := by
      rw [mul_pow, pow_mul, ← mul_assoc]
      gcongr
    _ ≤ _ := by
      gcongr
      exact theorem1013Parameters_bohr_radius_lower alpha halpha

/-- The ceiling-based `zeta` is small enough for Corollary 10.11 at the
actual, nonempty large-spectrum cardinality. -/
theorem theorem10_13_zeta_le_actualSpectrumRadius {N : Nat} [NeZero N]
    (alpha : Real) (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6)
    (K : Finset (ZMod N))
    (hKcard : (K.card : Real) ≤ section10SpectrumBound alpha)
    (hK : K.Nonempty) :
    section10Zeta alpha ≤
      (2 : Real) ^ (-((K.card : Real) + 4)) *
        section10BohrRadius alpha ^ K.card / K.card := by
  -- the bound at the ceiling parameter `k ≥ |K|` is antitone in `k`
  have hn : (0 : Real) < K.card := by exact_mod_cast hK.card_pos
  have hnk : (K.card : Real) ≤ section10SpectrumParameter alpha := hKcard.trans (Nat.le_ceil _)
  have hε := theorem10_13_bohrRadius_pos alpha halpha
  refine (theorem10_13_zeta_le_parameterRadius alpha halpha).trans ?_
  gcongr ?_ * ?_ / ?_
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · exact pow_le_pow_of_le_one hε.le (theorem10_13_bohrRadius_le_one alpha halpha halphaSixth)
      (by exact_mod_cast hnk)

end LeanProofs.GowersSzemeredi
