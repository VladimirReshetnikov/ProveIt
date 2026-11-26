import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelPartsRows

/-!
# Exact original-order derivative density identity

The two derivative products reduce to the preceding centered Bernoulli
density, the next centered density, and the literal signed Bernoulli
mean times the reciprocal-power weight.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsDensities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCenteredBernoulli (sample denominator_positive)
open GaussianStirlingAllOrderPanelDerivative
  (degreeProduct secondSample secondScaled signedMean second_complement second_scale)
open GaussianStirlingAllOrderPanelPartsRows (targetRow)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderReciprocalWeightError (weight derivative coefficient power)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open GaussianEuclideanDistanceName (fraction)
open GaussianFactorBudget (power_positive)
open GaussianRationalHorner (positive_product)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr negative_congr multiply_add multiply_negative multiply_associative add_commutative multiply_commutative)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowScalar (m : ℕ) : PTm n := fraction (num (degreeProduct m)) one
def highScalar (e : ℕ) : PTm n := fraction (coefficient e) one

def previousDensity (m e : ℕ) (U B M r : PTm n) : PTm n :=
  multiply (sample m r M) (weight e B M (gridDen U B M r))

def nextDensity (m e : ℕ) (U B M r : PTm n) : PTm n :=
  multiply (sample (m+1) r M) (weight (e+2) B M (gridDen U B M r))

def meanDensity (m e : ℕ) (U B M r : PTm n) : PTm n :=
  multiply (signedMean m) (weight e B M (gridDen U B M r))

theorem density_identity (m e : ℕ) (U B M r : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] targetRow m e U B M r ≐
      sub (multiply (lowScalar m) (sub (meanDensity m e U B M r) (previousDensity m e U B M r)))
        (multiply (highScalar e) (nextDensity m e U B M r)) := by
  let D := gridDen U B M r
  let S := sample m r M
  let C : PTm n := signedMean m
  let H := sample (m+1) r M
  let W := weight e B M D
  let V := weight (e+2) B M D
  let L := lowScalar (n := n) m
  let K := highScalar (n := n) e
  have hD : Γ ⊢[PRAAx] le one D :=
    le_trans (positive_product _ _ hU hM) (le_add_right _ _)
  have ht := second_complement m r M hM
  have hS : Γ ⊢[PRAAx] secondScaled m r M ≐ sub C S := by
    apply Prf.eqTrans (add_negative_cancel (secondScaled m r M) S
      (RationalNormalForm.normalize_well_formed _ _ (denominator_positive m M hM))).eqSymm
    exact add_congr ((add_commutative _ _).eqTrans ht) (.eqRefl _)
  have hL : Γ ⊢[PRAAx] secondSample m r M ≐ multiply L (sub C S) :=
    (second_scale m r M hM).eqSymm.eqTrans (multiply_congr (.eqRefl _) hS)
  have hV : Γ ⊢[PRAAx] derivative e D B M ≐ multiply K V := by
    have hP : Γ ⊢[PRAAx] le one (power (e+2) D) := power_positive _ _ hD
    exact (fraction_congr (.eqRefl _) (one_mul _).eqSymm).eqTrans
      (fraction_multiply (coefficient e) one (power (e+2) (B*M)) (power (e+2) D) (le_refl one) hP).eqSymm
  have e₁ : Γ ⊢[PRAAx] multiply (secondSample m r M) W ≐ multiply L (sub (multiply C W) (multiply S W)) :=
    (multiply_congr hL (.eqRefl _)).eqTrans ((multiply_associative _ _ _).eqTrans
      (multiply_congr (.eqRefl _) ((multiply_commutative _ _).eqTrans
        ((multiply_add _ _ _).eqTrans (add_congr (multiply_commutative _ _)
          ((multiply_negative _ _).eqTrans (negative_congr (multiply_commutative _ _))))))))
  have e₂ : Γ ⊢[PRAAx] multiply H (derivative e D B M) ≐ multiply K (multiply H V) :=
    (multiply_congr (.eqRefl _) hV).eqTrans ((multiply_associative _ _ _).eqSymm.eqTrans
      ((multiply_congr (multiply_commutative _ _) (.eqRefl _)).eqTrans (multiply_associative _ _ _)))
  exact add_congr e₁ (negative_congr e₂)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsDensities
