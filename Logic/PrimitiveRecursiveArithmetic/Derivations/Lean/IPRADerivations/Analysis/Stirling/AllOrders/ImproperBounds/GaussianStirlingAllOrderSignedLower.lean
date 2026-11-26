import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedLowerAlgebra
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderImproperPositive
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod

/-!
# Strict sign of the original log-Stirling truncation error

The original remainder minus its literal first m correction terms
has positive value after multiplication by (-1)^m. The name is the
actual product with the signed residual. Multiplication by the
positive denominator 2m+2 recovers the original positive improper
kernel, and reflection of named order proves the strict endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedNaturalScaleOrder (reflect_strict)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderImproperPositive (original_improper_positive)
open GaussianStirlingAllOrderLogTruncation
  (errorF errorData signedF signedData error_regular original_logarithmic_truncation)
open GaussianStirlingAllOrderPanelPartsNames (constantCap constant_bound)
open GaussianStirlingAllOrderSignedLowerAlgebra
  (orientationPoint denominator_positive cancel_orientation_and_denominator)
open GaussianStirlingAllOrderTruncationAlgebra (signedScale)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianStirlingOddCoefficients (fraction_embed)
open GaussianArctangentExponentialPeriod (constant_product)
open RationalGaussianEmbedding (embed_zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "I" => GaussianStirlingAllOrderImproperName.nameF
local notation "idata" => GaussianStirlingAllOrderImproperName.data

def orientedF : PR 2 := multiplyF C errorF
def orientedData (m : ℕ) (A B x : PTm n) : PTm n :=
  multiplyData C errorF (orientationPoint m) (errorData m A B x)

@[simp] theorem subst_orientedData {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B x : PTm n) :
    Syn.subst σ (orientedData m A B x) = orientedData m (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) :=
  by simp [orientedData]

theorem oriented_regular (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN orientedF (orientedData m A B x) :=
  multiply_fast _ _ _ _ (constant_regular _) (error_regular m A B x hs)

def zeroPoint : PTm n := GaussianPositiveRationalLogarithm.fraction zero one

private theorem one_constant (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent C GaussianNameRingLaws.oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (GaussianNameRingLaws.one_fast _)
  refine .allI ?_
  simpa [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalReciprocal.qone] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qone).eqTrans
      (GaussianNameRingLaws.one_at (var 0) (Syn.shift x)).eqSymm

private theorem zero_point (t : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (productF C) C (productData C t zeroPoint) zeroPoint := by
  have q : Γ ⊢[PRAAx] zeroPoint ≐ qzero :=
    (fraction_embed zero one (le_refl one)).eqSymm.eqTrans embed_zero
  have e : Γ ⊢[PRAAx] qmul (naturalPoint t) zeroPoint ≐ zeroPoint :=
    (qmul_congr (.eqRefl _) q).eqTrans ((qmul_zero_right _).eqTrans q.eqSymm)
  exact cross_trans _ _ _ _ _ _ (constant_product _ _) (constant_equal_cross _ _ e)

set_option maxHeartbeats 700000 in
theorem denominator_scaled_oriented (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (productF orientedF) (I m)
      (productData orientedF (num (2*m+2)) (orientedData m A B x)) (idata m A B) := by
  let T := naturalPoint (num (2*m+2) : PTm n)
  let S := orientationPoint (n := n) m
  let U := signedScale (n := n) m
  let W := idata m A B
  let F := I m
  let F' := multiplyF C F
  let w := multiplyData C F U W
  let G := multiplyF C C
  let g := multiplyData C C T S
  let V := multiplyF G C
  let v := multiplyData G C g U
  let gw := qmul T S
  have hcT := constant_regular (Γ := Γ) T
  have hcS := constant_regular (Γ := Γ) S
  have hcU := constant_regular (Γ := Γ) U
  have hcV := GaussianNameRingLaws.one_fast (Γ := Γ) W
  have hg := multiply_fast _ _ _ _ hcT hcS
  have hv := multiply_fast _ _ _ _ hg hcU
  have hf := GaussianStirlingAllOrderImproperName.name_regular m A B x hs
  have hw := multiply_fast _ _ _ _ hcU hf
  have he := error_regular m A B x hs
  have cx : Γ ⊢[PRAAx] crossEquivalent errorF F' (errorData m A B x) w :=
    cross_trans _ _ _ _ _ _
      (cross_symm _ _ _ _ (original_logarithmic_truncation m A B x hs))
      (GaussianBoundedConstantProductName.ordinary_product_identity F (constantCap U) U W
        (.andI hf (constant_bound U)))
  have a := multiply_cross C C errorF F' S S (errorData m A B x) w hcS hcS he hw
    (cross_refl _ _ hcS) cx
  have b := multiply_cross C C orientedF (multiplyF C F') T T (orientedData m A B x) (multiplyData C F' S w)
    hcT hcT (oriented_regular m A B x hs) (multiply_fast _ _ _ _ hcS hw) (cross_refl _ _ hcT) a
  have group := cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative C C F' T S w hcT hcS hw)
  have group' := cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative G C F g U W hg hcU hf)
  have const := multiply_cross G C C C g gw U U hg (constant_regular _) hcU hcU
    (constant_product T S) (cross_refl _ _ hcU)
  have cut := cross_trans _ _ _ _ _ _ const
    (cross_trans _ _ _ _ _ _ (constant_product gw U)
      (constant_equal_cross _ _ (cancel_orientation_and_denominator m)))
  have cutOne := cross_trans _ _ _ _ _ _ cut (one_constant W)
  have replace := multiply_cross V GaussianNameRingLaws.oneF F F v W W W hv hcV hf hf cutOne (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ b
    (cross_trans _ _ _ _ _ _ group (cross_trans _ _ _ _ _ _ group'
      (cross_trans _ _ _ _ _ _ replace (GaussianNameRingLaws.multiply_one_left F W hf))))

theorem original_strict_oriented_error_lower (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder C orientedF zeroPoint (orientedData m A B x) := by
  let t : PTm n := num (2*m+2)
  have h := original_improper_positive m A B x hs
  have trans := strict_transport _ _ _ _ _ _ _ _ (zero_point t)
    (cross_symm _ _ _ _ (denominator_scaled_oriented m A B x hs)) h
  exact reflect_strict C orientedF t zeroPoint (orientedData m A B x)
    (denominator_positive m) (constant_regular _) (oriented_regular m A B x hs) trans

theorem actual_all_order_oriented_log_Stirling_strict_lower_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (source (var 0) (var 1) ⟶
      strictOrder C orientedF zeroPoint (orientedData m (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_strict_oriented_error_lower m _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedLower
