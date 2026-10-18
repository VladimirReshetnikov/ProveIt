import GowersSzemeredi.Proofs16BaseCaseExtraction
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Finite-family assembly for the repaired Lemma 16.3

This module keeps `lemma163Alpha_le_gammaInvSq`; the rest of the development,
with its description, is in `Proofs16BaseCaseAssemblySide`, outside the final
route. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma lemma163Alpha_le_gammaInvSq {gamma theta : Real}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    lemma163Alpha gamma theta ≤ gamma ^ (-(2 : Int)) := by
  have ha : 0 ≤ gamma * theta := by positivity
  have haOne : gamma * theta ≤ 1 := by
    calc
      gamma * theta ≤ 1 * 1 :=
        mul_le_mul hgammaOne hthetaOne htheta.le (by norm_num)
      _ = 1 := by norm_num
  have halphaOne : lemma163Alpha gamma theta ≤ 1 := by
    unfold lemma163Alpha
    have hpow : (gamma * theta) ^ (10000 : Nat) ≤ 1 := pow_le_one₀ ha haOne
    have htwo : (2 : Real) ^ (-(2000 : Real)) ≤ 1 := by
      calc
        (2 : Real) ^ (-(2000 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 1 := by simp
    calc
      (2 : Real) ^ (-(2000 : Real)) * (gamma * theta) ^ (10000 : Nat) ≤
          1 * 1 := mul_le_mul htwo hpow (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hone : (1 : Real) ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg]
    have hsq : gamma ^ (2 : Nat) ≤ 1 := pow_le_one₀ hgamma.le hgammaOne
    exact (one_le_inv₀ (by positivity)).2 hsq
  exact halphaOne.trans hone

end LeanProofs.GowersSzemeredi.BaseCase
