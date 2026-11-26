import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.GaussianRationalConstantProductRate
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianL1
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedSize
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Normalizing the first-order comparison by a native Gaussian step

A first-order comparison for the actual named increment gives an
independent rate for the actual divided difference. The multiplier is
bounded by twice the denominator of the step divided by its numerator's
L1 norm. The reciprocal cancels exactly in the ordinary named product.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianNativeDerivativeQuotientRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNamedDifferenceQuotient (separated inverse actual_inverse)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (qone)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Prod" => GaussianBoundedConstantProductName.nameF
local notation "pd" => GaussianBoundedConstantProductName.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem norm1_positive (h : PTm n) (hn : Γ ⊢[PRAAx] le one (normSq h)) :
    Γ ⊢[PRAAx] le one (norm1 h) := by
  refine .orE (lt_or_le zero (norm1 h)) Prf.hyp0 ?_
  have hz : (le (norm1 h) zero :: Γ) ⊢[PRAAx] norm1 h ≐ zero :=
    le_antisymm Prf.hyp0 (zero_le _)
  have small := le_congr (.eqRefl _) ((congrMul hz hz).eqTrans (mul_zero zero))
    (GaussianL1.normSq_le_norm1_square h).wk
  exact not_succ_le_self zero _ (le_trans hn.wk small)

private theorem two_positive : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one

private theorem reciprocal_bound (h B : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B) :
    Γ ⊢[PRAAx] bounded (GaussianNamedDifferenceQuotient.inverse h B) (two*B) (norm1 h) := by
  have hB := hs.andE₁
  have hA := positive_product two B two_positive hB
  apply GaussianRationalLowerBounds.inverse_bound _ _ _ (norm1_positive h hs.andE₂) hA
  apply GaussianRationalLowerBounds.lower_from_representation _ h B _ _ hB hA (ofGaussian_represents h B hB)
  have step := GaussianL1.norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl step+2*𝔞(normSq h))

private theorem cancel_product (D : PR 2) (w h B : PTm n)
    (hd : Γ ⊢[PRAAx] pointCN D w)
    (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h B) : Γ ⊢[PRAAx]
    crossEquivalent
      (multiplyF constantF (multiplyF constantF D)) D
      (multiplyData constantF (multiplyF constantF D) (GaussianNamedDifferenceQuotient.inverse h B)
        (multiplyData constantF D (ofGaussian h B) w)) w := by
  let c := GaussianNamedDifferenceQuotient.inverse h B
  let a := ofGaussian h B
  let P := multiplyF constantF constantF
  let t := multiplyData constantF constantF c a
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF D c a w
    (constant_regular c) (constant_regular a) hd
  have hc := GaussianGammaDigammaTwoShiftNamedSize.constant_product c a qone
    (GaussianNamedDifferenceQuotient.actual_inverse h B hs)
  have hc₁ := cross_trans _ _ _ _ _ _ hc (GaussianArctangentExponentialPeriod.constant_one_cross w)
  have hp := GaussianNameArithmetic.multiply_fast (Γ := Γ) constantF constantF c a (constant_regular c) (constant_regular a)
  have prod := GaussianGammaAdjacentCutoff.multiply_cross P GaussianNameRingLaws.oneF D D t w w w
    hp (GaussianNameRingLaws.one_fast w) hd hd hc₁ (cross_refl D w hd)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc)
    (cross_trans _ _ _ _ _ _ prod (GaussianNameRingLaws.multiply_one_left D w hd))


theorem rate (f g D : PR 2) (x y w h B M K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hd : Γ ⊢[PRAAx] pointCN D w)
    (hs : Γ ⊢[PRAAx] separated h B) (hK : Γ ⊢[PRAAx] le one K)
    (hr : Γ ⊢[PRAAx] independentRate (Diff f g) (multiplyF constantF D) (dd x y)
      (multiplyData constantF D (ofGaussian h B) w) M K) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedDifferenceQuotient.nameF f g) D
      (GaussianNamedDifferenceQuotient.data f g x y h B) w ((two*B)*M) (norm1 h*K) := by
  let F := Diff f g
  let G := multiplyF constantF D
  let u := dd x y
  let v := multiplyData constantF D (ofGaussian h B) w
  let A : PTm n := two*B
  let c := inverse h B
  let H := norm1 h
  have hH := norm1_positive h hs.andE₂
  have hc := reciprocal_bound h B hs
  have hu := GaussianNamedDifference.name_regular f g x y hf hg
  have hv := GaussianNameArithmetic.multiply_fast constantF D (ofGaussian h B) w (constant_regular _) hd
  have mulRate := GaussianRationalConstantProductRate.rate F G A H c u v M K hH hK hc hr
  have bound := GaussianRationalConstantProductRate.integral_bound c A H hH hc
  have left := GaussianBoundedConstantProductName.ordinary_product_identity F A c u (.andI hu bound)
  have right := GaussianBoundedConstantProductName.ordinary_product_identity G A c v (.andI hv bound)
  have canon := cross_trans _ _ _ _ _ _ right (cancel_product D w h B hd hs)
  exact GaussianNamedRateTransport.transport (Prod F) (Prod G) (GaussianNamedDifferenceQuotient.nameF f g) D
    (pd A c u) (pd A c v) (GaussianNamedDifferenceQuotient.data f g x y h B) w _ _
    (positive_product _ _ hH hK) mulRate (cross_symm _ _ _ _ left) (cross_symm _ _ _ _ canon)

end LeanProofs.IPRA.Analysis.GaussianNativeDerivativeQuotientRate
