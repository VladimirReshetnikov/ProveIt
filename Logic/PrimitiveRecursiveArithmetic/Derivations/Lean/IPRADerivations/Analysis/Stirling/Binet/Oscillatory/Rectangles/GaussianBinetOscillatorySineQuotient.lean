import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatoryColumns
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius

/-!
# Positive-time sine quotient of the actual transposed cosine column

At a positive damping mesh point the frequency coefficient has the
explicit inverse bound given by the mesh denominator. Multiply the
actual cleared cosine comparison by that inverse after transporting
through the original complex damping.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineQuotient

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianBinetCosinePrimitive (cosineValue endpoint cleared_error)
open GaussianBinetExponentialIntegral (numerator)
open GaussianBinetExponentialPanel (unit_bound)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (exponent_scale coefficient_congr)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatoryColumns (damping columnTarget column_error)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qmul_canonical positive_product ofGaussian_represents)
open GaussianRationalLowerBounds (lower lower_from_representation name_lower inverse_bound)
open GaussianRationalMetric (bounded distanceBounded qnegative_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotient (p A B C S N : PTm n) : PTm n :=
  qmul (reciprocal (coefficient S N (polarity true))) (endpoint p (A*S) (B*N) C one)
def target (j p X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  qmul (damping p X Y D sign T j N R) (quotient (p+N) A B (U*T) (T*j) N)

private theorem imaginary_lower (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    lower (coefficient A B (polarity true)) A B := by
  let c := coefficient A B (polarity true)
  let z := native zero A (polarity true)
  let v := ComplexLogarithmRemainder.neg z
  have h : Γ ⊢[PRAAx] normSq v ≐ A*A := (ComplexLogarithmRemainder.normSq_neg z).eqTrans
    ((GaussianLogGammaEulerResidualRadius.native_norm zero A (polarity true) (.orI₂ (.eqRefl one))).eqTrans (by ipra_ring))
  have rep := qnegative_represents (argument zero A B (polarity true)) z B (ofGaussian_represents (Γ := Γ) z B hB)
  exact lower_from_representation c v B A B hB hB rep
    (le_congr (by ipra_ring) (congrMul (.eqRefl (B*B)) h.eqSymm) (le_refl ((B*B)*(A*A))))

private theorem damping_bound (p j X Y D sign R T N : PTm n) (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] bounded (damping p X Y D sign T j N R) two one := by
  have time := le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)
  have hb := GaussianBinetLaplaceExponential.exponent_bound X Y D sign R T (T*j) N hz hN time
  exact unit_bound (p+N) _ _ (GaussianSignedNameExponentialOrder.constant_input _ _ hb)
    (GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign (T*j) N hz.andE₁.andE₂ hN)

theorem quotient_error (j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L)
    (hA : Γ ⊢[PRAAx] le A (B*U)) (hj₁ : Γ ⊢[PRAAx] le one j) (hj : Γ ⊢[PRAAx] le j N)
    (hC : Γ ⊢[PRAAx] le (U*(D*L)) M) : Γ ⊢[PRAAx]
    distanceBounded (columnTarget j p M X Y D sign A B R U L N) (target j p X Y D sign A B R U L N)
      (N*(two*numerator (p+N) (U*(D*L)) one M)) (unit (p+N)*M) := by
  let T := D*L
  let S := T*j
  let C := U*T
  let k := coefficient S N (polarity true)
  let c := coefficient (A*S) (B*N) (polarity true)
  let r := p+N
  let e := damping p X Y D sign T j N R
  let u := cosineValue r (A*S) (B*N) C one M
  let v := endpoint r (A*S) (B*N) C one
  let w := fraction A B
  let x := qmul e (qmul w u)
  let F := numerator r C one M
  let H := unit r*M
  have hH := positive_product (Γ := Γ) _ _ (unit_positive r) hM
  have hE := positive_product _ _ hB hN
  have hS := positive_product _ _ (positive_product _ _ hz.andE₁.andE₂ hL) hj₁
  have angle : Γ ⊢[PRAAx] le (A*S) (C*(B*N)) :=
    le_congr (.eqRefl _) (by dsimp only [C,T]; ipra_ring)
      (le_mul_mono hA (le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)))
  have radius : Γ ⊢[PRAAx] le (C*one) M := le_congr (by dsimp only [C,T]; ipra_ring) (.eqRefl _) hC
  have cleared := cleared_error r (A*S) (B*N) C one M hE angle hM radius
  have b := damping_bound p j X Y D sign R T N hz hN hj
  have scaled := GaussianApproximateInverseDistance.multiply_distance e _ _ two F H hH b cleared
  have exact_angle : Γ ⊢[PRAAx] qmul k w ≐ c :=
    (exponent_scale true S N A B hN hB).eqTrans (coefficient_congr true (mul_comm _ _) (mul_comm _ _))
  have kx : Γ ⊢[PRAAx] qmul k x ≐ qmul e (qmul c u) :=
    (GaussianRationalPowerAlgebra.commute_nested k e (qmul w u)).eqTrans
      (qmul_congr (.eqRefl _) ((qmul_associative k w u).eqSymm.eqTrans (qmul_congr exact_angle (.eqRefl _))))
  have admit := imaginary_lower S N hN
  have nonzero := GaussianNameReciprocal.lower_norm_positive k N hN (name_lower k S N hS hN admit)
  have inverseRadius : Γ ⊢[PRAAx] le (N*one) (N*S) := by
    change Γ ⊢[PRAAx] le (N*one) (N*(D*L*j))
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right N hS)
  have inv : Γ ⊢[PRAAx] bounded (reciprocal k) N one :=
    bounded_radius_mono _ _ _ _ _ hS (le_refl one) inverseRadius
      (inverse_bound k S N hS hN admit)
  have with_k : Γ ⊢[PRAAx] distanceBounded (qmul k x) (qmul e v) (two*F) H :=
    distance_congr kx.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) scaled
  have first : Γ ⊢[PRAAx] qmul (reciprocal k) (qmul k x) ≐ x :=
    (qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative _ _).eqTrans (reciprocal_identity k nonzero)) (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right x (qmul_canonical _ _))))
  have last : Γ ⊢[PRAAx] qmul (reciprocal k) (qmul e v) ≐ qmul e (qmul (reciprocal k) v) :=
    GaussianRationalPowerAlgebra.commute_nested (reciprocal k) e v
  exact distance_congr first last (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (reciprocal k) _ _ N (two*F) H hH inv with_k)

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineQuotient
