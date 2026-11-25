import IPRADerivations.Analysis.GaussianGammaRationalLogWendel
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.Analysis.GaussianNamedNaturalScaleOrder
import IPRADerivations.Analysis.GaussianGammaEulerDenominator

/-!
# Width of a positive rational logarithmic window

For positive integers r, b and a natural increment c, the exact named
increase from log(r/b) to log((r+c)/b), multiplied by a, is at most ac/r.
-/

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupLogWindow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalNaturalScale (naturalPoint)
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => productF H
local notation "ld" => productData H

theorem scaled_log_sum (a r b t : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hr : Γ ⊢[PRAAx] le one r) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent (addF L L) L (addData (ld t (hd a r)) (ld t (hd r b))) (ld t (hd a b)) := by
  let q := naturalPoint t
  let x := hd a r
  let y := hd r b
  let z := hd a b
  have hq := constant_regular (Γ := Γ) q
  have hx := GaussianHarmonicLogarithmName.name_regular a r (.andI ha hr)
  have hy := GaussianHarmonicLogarithmName.name_regular r b (.andI hr hb)
  have hz := GaussianHarmonicLogarithmName.name_regular a b (.andI ha hb)
  have split := GaussianNameRingLaws.distributive constantF H H q x y hq hx hy
  have fold := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (addF H H) H q q (addData x y) z
    hq hq (add_fast _ _ _ _ hx hy) hz (cross_refl _ _ hq)
    (GaussianGammaRationalLogWendel.log_ratio_sum a r b ha hr hb)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split) fold

theorem unscaled_window_order (r c : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] realOrder H constantF (hd (r+c) r) (fraction c r) := by
  have hh : Γ ⊢[PRAAx] le one (r+c) := le_trans hr (le_add_right _ _)
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _
      (GaussianHarmonicLogarithmName.cross_original (r+c) r (.andI hh hr)))
    (cross_refl _ _ (constant_regular _)) (GaussianStirlingMultiplicativeBoundsLog.logarithm_rectangles r c hr).andE₂

theorem window_order (r b c t : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder L (addF (productF constantF) L)
      (ld t (hd (r+c) b)) (addData (productData constantF t (fraction c r)) (ld t (hd r b))) := by
  let x := hd (r+c) r
  let y := hd r b
  let z := fraction c r
  have h : Γ ⊢[PRAAx] le one (r+c) := le_trans hr (le_add_right _ _)
  have hx := GaussianHarmonicLogarithmName.name_regular (r+c) r (.andI h hr)
  have hz := constant_regular (Γ := Γ) z
  have hy := multiply_fast constantF H _ _ (constant_regular (naturalPoint t))
    (GaussianHarmonicLogarithmName.name_regular r b (.andI hr hb))
  have scale := GaussianNamedNaturalScaleOrder.preserve_order H constantF t x z hx hz
    (unscaled_window_order r c hr)
  have sum := add_order L (productF constantF) L L (ld t x) (productData constantF t z) (ld t y) (ld t y)
    scale (order_refl _ _ hy)
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (scaled_log_sum (r+c) r b t h hr hb))
    (cross_refl _ _ (add_fast _ _ _ _
      (multiply_fast constantF constantF _ _ (constant_regular (naturalPoint t)) hz) hy)) sum

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupLogWindow
