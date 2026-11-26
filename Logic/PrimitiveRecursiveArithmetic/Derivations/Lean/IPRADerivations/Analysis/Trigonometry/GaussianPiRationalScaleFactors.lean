import IPRADerivations.Analysis.Trigonometry.GaussianPiRationalScale
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant

/-!
# Factoring signed π steps through a positive rational step

The two step names for (±π/D) are exactly the original named π
with the sign and the positive step kept as separate factors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPiRationalScaleFactors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative)
open GaussianPiRationalScale (nameF data point native)
open GaussianRationalHorner (qmul ofGaussian_represents ofGaussian_canonical qmul_represents qmul_canonical
  canonical_unique represents_congr)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_neg im_neg)
open GaussianSineProductImaginaryLogDerivative (rationalReal realNumerator)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Pi" => GaussianGammaHalfPiName.nameF

def signedF : PR 2 := multiplyF constantF Pi
def signedData (s : Bool) (x : PTm n) : PTm n := multiplyData constantF Pi (point s one one) x

theorem signed_regular (s : Bool) (x : PTm n) : Γ ⊢[PRAAx] pointCN signedF (signedData s x) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianGammaHalfPiName.name_regular x)

theorem step_coefficient (s : Bool) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qmul (rationalReal one D) (point s one one) ≐ point s one D := by
  have raw := qmul_represents _ _ _ _ _ _ hD (le_refl one)
    (ofGaussian_represents (Γ := Γ) (realNumerator one) D hD) (ofGaussian_represents (native s one) one (le_refl one))
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul (realNumerator one) (native s one)) (native s one) := by
    cases s <;> apply equal_of_values <;>
      simp [native,re_mul,im_mul,re_neg,im_neg,realNumerator,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  exact canonical_unique _ _ _ D (qmul_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) e (by ipra_ring) raw) (ofGaussian_represents _ _ hD)

theorem split_step (s : Bool) (D R x : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] le one (R*D)) :
    Γ ⊢[PRAAx] crossEquivalent nameF (multiplyF constantF signedF) (data s one D R x)
      (multiplyData constantF signedF (rationalReal one D) (signedData s x)) := by
  let a := rationalReal one D
  let b : PTm n := point s one one
  let c := point s one D
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hc := constant_regular (Γ := Γ) c
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have fixed := cross_trans (multiplyF constantF constantF) constantF constantF
    (multiplyData constantF constantF a b) (qmul a b) c
    (constant_product_cross a b) (constant_data_cross _ _ (step_coefficient s D hD))
  have lift := multiply_cross (multiplyF constantF constantF) constantF Pi Pi
    (multiplyData constantF constantF a b) c x x (multiply_fast _ _ _ _ ha hb) hc hp hp fixed (cross_refl Pi x hp)
  exact cross_trans _ _ _ _ _ _ (GaussianPiRationalScale.ordinary s one D R x hD h)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ lift) (multiply_associative constantF constantF Pi a b x ha hb hp))

end LeanProofs.IPRA.Analysis.GaussianPiRationalScaleFactors
