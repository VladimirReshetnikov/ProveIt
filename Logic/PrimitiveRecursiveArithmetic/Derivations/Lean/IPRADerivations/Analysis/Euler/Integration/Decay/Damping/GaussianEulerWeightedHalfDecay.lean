import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayProduct
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerBound
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport

/-!
# Combining the real monomial and the first half-decay factor

The actual half-decay observation has a bound obtained by dividing
the checked weighted decay estimate by the exact positive monomial.
An observation of the complex power with error `2^-p` then gives
the factorial majorant for the first product, with explicit slack.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerWeightedHalfDecay

open_ipra
open GaussianEulerIntegrandName (decayF decayData powerF powerData)
open GaussianEulerHalfDecayProduct (halfWeightedF halfWeightedData)
open GaussianEulerUpperPowerOrder (source)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianDominantPairAlgebra (radiusPoint radius_one radius_bounded radius_congr radius_power radius_multiply)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianRationalReciprocal (power bounded_product bound_congr)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open RationalGaussianEmbedding (embed)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def majorant (R : PTm n) : PTm n := unit R*fact R
def slack (a R : PTm n) : PTm n := two*pw (two*a) R
def productSlack (a R : PTm n) : PTm n := majorant R+two*slack a R
def halfSample (p a b : PTm n) : PTm n := ap2 decayF p (decayData a (two*b))

ipra_subst majorant [fact]

ipra_subst productSlack [slack]

ipra_subst halfSample [decayData, GaussianGammaFiniteApproximantName.exponentialInputData]

theorem radius_embedding (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] embed (fraction a b) ≐ radiusPoint a b :=
  (GaussianEulerDecayOrder.fraction_embedding a b hb).eqTrans (fraction_is_radius_point a b hb)

theorem radius_rescale (a b c : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) :
    Γ ⊢[PRAAx] radiusPoint (a*c) (b*c) ≐ radiusPoint a b :=
  (radius_embedding _ _ (positive_product _ _ hb hc)).eqSymm.eqTrans
    ((RationalGaussianRealPart.embed_congr (RationalConvexClockRescale.fraction_rescale a b c hb hc)).eqTrans
      (radius_embedding a b hb))

theorem radius_reciprocal (a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (radiusPoint b a) (radiusPoint a b) ≐ qone := by
  have hr := positive_product _ _ ha hb
  exact (radius_multiply b a a b ha hb).eqTrans
    ((radius_congr (by ipra_ring) (one_mul _).eqSymm).eqTrans
      ((radius_rescale one one (a*b) (le_refl one) hr).eqTrans radius_one))

theorem half_decay_monomial_bound (p a b R : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (halfSample p a b) ((majorant R*unit p+slack a R)*pw b R) (unit p*pw a R) := by
  let A := pw a R
  let B := pw b R
  let x := halfSample p a b
  let w := radiusPoint A B
  let v := radiusPoint B A
  have hA : Γ ⊢[PRAAx] le one A := GaussianPolynomialPerturbation.power_positive a R ha
  have hB : Γ ⊢[PRAAx] le one B := GaussianPolynomialPerturbation.power_positive b R hb
  have hh := positive_product _ _ (le_succ_self one) hb
  have e : Γ ⊢[PRAAx] radiusPoint (two*a) (two*b) ≐ radiusPoint (a*two) (b*two) :=
    radius_congr (mul_comm two a) (mul_comm two b)
  have scale := e.eqTrans (radius_rescale a b two hb (le_succ_self one))
  have weight : Γ ⊢[PRAAx] power (radiusPoint (two*a) (two*b)) R ≐ w :=
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl R) scale).eqTrans (radius_power a b R hb)
  have hx : Γ ⊢[PRAAx] bounded (qmul w x) (majorant R*unit p+slack a R) (unit p) :=
    bound_congr (qmul_congr weight (.eqRefl x)) (.eqRefl _) (.eqRefl _)
      (GaussianEulerDecayFactorBounds.original_half_decay_factor_bound a (two*b) R p ha hh)
  have hInv := bounded_product (qmul w x) v _ _ B A (unit_positive p) hA hx (radius_bounded B A hA)
  have same : Γ ⊢[PRAAx] qmul (qmul w x) v ≐ x :=
    (GaussianRationalPowerAlgebra.qmul_commutative (qmul w x) v).eqTrans
      ((GaussianReciprocalHorner.qmul_associative v w x).eqSymm.eqTrans
        ((qmul_congr (radius_reciprocal A B hA hB) (.eqRefl x)).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical x
            (GaussianRadiusExponentialName.sample_canonical _ _ _ _))))
  exact bound_congr same (.eqRefl _) (.eqRefl _) hInv

theorem approximate_power_times_half_decay (q p a b R : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hq : Γ ⊢[PRAAx] bounded q (pw a R*unit p+pw b R) (pw b R*unit p)) :
    Γ ⊢[PRAAx] bounded (qmul q (halfSample p a b)) (majorant R*unit p+productSlack a R) (unit p) := by
  let A := pw a R
  let B := pw b R
  let U := unit p
  let M := majorant R
  let K := slack a R
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have ha := le_trans hb hab
  have hA : Γ ⊢[PRAAx] le one A := GaussianPolynomialPerturbation.power_positive a R ha
  have hB : Γ ⊢[PRAAx] le one B := GaussianPolynomialPerturbation.power_positive b R hb
  have d := positive_product _ _ hB hu
  have s := positive_product _ _ hu hA
  have w := bounded_product q (halfSample p a b) _ _ _ _ d s hq (half_decay_monomial_bound p a b R ha hb)
  have h1 : Γ ⊢[PRAAx] le (A*U+B) (A*U+A) := add_le_add₂ (le_refl (A*U)) (pw_le_pw R hab)
  have h2 : Γ ⊢[PRAAx] le ((A*U+B)*(M*U+K)) ((A*U+A)*(M*U+K)) :=
    mul_le_mul_right (M*U+K) h1
  have h3 : Γ ⊢[PRAAx] le ((A*U+A)*(M*U+K)) (A*U*(M*U+M+two*K)) := by
    have grow : Γ ⊢[PRAAx] le (A*K) (A*K*U) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (A*K) hu)
    exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (A*U*(M*U+M+K))) grow)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ d s) hu _ w
  exact le_congr (by ipra_ring) (by unfold productSlack; dsimp only [A,B,U,M,K]; ipra_ring)
    (mul_le_mul_right (B*U) (le_trans h2 h3))

theorem original_weighted_half_decay_sample (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] bounded (ap2 halfWeightedF p (halfWeightedData z B a b))
      (majorant R*unit p+productSlack a R) (unit p) := by
  let P := powerData z B a b
  let H := decayData a (two*b)
  let s := productClock powerF decayF P H p
  let M := majorant R
  let K := productSlack a R
  have e := product_at (Γ := Γ) powerF decayF P H p
  have claim := approximate_power_times_half_decay (ap2 powerF s P) s a b R
    h.andE₂.andE₁.andE₂ h.andE₂.andE₂ (GaussianEulerUpperPowerBound.original_power_bound s z R B a b h)
  have order : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right p _)
  have cmp : Γ ⊢[PRAAx] le ((M*unit s+K)*unit p) ((M*unit p+K)*unit s) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (M*unit p*unit s)) (mul_le_mul_right K order))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (unit_positive s) (unit_positive p) cmp claim)

theorem actual_monomial_weighted_half_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le (var 3) (var 2) ⟶
      bounded (var 0) (pw (var 2) (var 4)*unit (var 1)+pw (var 3) (var 4)) (pw (var 3) (var 4)*unit (var 1)) ⟶
      bounded (qmul (var 0) (halfSample (var 1) (var 2) (var 3)))
        (majorant (var 4)*unit (var 1)+productSlack (var 2) (var 4)) (unit (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (approximate_power_times_half_decay _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_weighted_Euler_half_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (ap2 halfWeightedF (var 0) (halfWeightedData (var 1) (var 3) (var 4) (var 5)))
        (majorant (var 2)*unit (var 0)+productSlack (var 4) (var 2)) (unit (var 0))) :=
  closeUniv 6 (.impI (original_weighted_half_decay_sample _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerWeightedHalfDecay
