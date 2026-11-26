import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTransformedPower
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# Sharp original Euler-integrand norm at transformed lower times

The unchanged original power samples have radius (b/a)^(A-1)+eps.
The actual decay has radius 1+2eps from its existing reciprocal
representative. At the true original product clock their product has a
computed dyadic envelope. The actual integrand/product equivalence and
one finite Euclidean gap query leave exactly (b/a)^(A-1)+2^-p at the
unchanged original integrand observation p.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTransformedIntegrand

open_ipra
open GaussianEulerLowerPowerOrder (source)
open GaussianEulerIntegrandName (powerF powerData decayF decayData nameF data productF productData)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def S (A b : PTm n) : PTm n := pw b (pred A)
def T (A a : PTm n) : PTm n := pw a (pred A)
def productCost (A a b : PTm n) : PTm n := two*S A b+(two+one)*T A a
def cost (A a b : PTm n) : PTm n := productCost A a b+T A a
def query (p z B A a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF decayF (powerData z B (pw a A) (pw b A)) (decayData (pw a A) (pw b A))) p
def observation (p z B A a b : PTm n) : PTm n := ap2 nameF p (data z B (pw a A) (pw b A))
ipra_subst S
ipra_subst T
ipra_subst productCost
ipra_subst cost
ipra_subst observation

theorem decay_bound (a b p : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (ap2 decayF p (decayData a b)) (unit p+two) (unit p) := by
  have raw := GaussianEulerDecayFactorBounds.original_half_decay_factor_bound a b zero p ha hb
  have e : Γ ⊢[PRAAx] qmul (GaussianRationalReciprocal.power (GaussianDominantPairAlgebra.radiusPoint (two*a) b) zero)
      (ap2 decayF p (decayData a b)) ≐ ap2 decayF p (decayData a b) :=
    (GaussianRationalSyntheticDivision.qmul_congr (GaussianRationalReciprocal.power_zero _) (.eqRefl _)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRadiusExponentialName.sample_canonical GaussianGammaCanonicalExponent.constantF _ p (GaussianEulerIntegrandName.decayPoint a b))))
  have radius : Γ ⊢[PRAAx] unit zero*Products.fact zero*unit p+two*pw (two*a) zero ≐ unit p+two :=
    (congrAdd (congrMul (congrMul (pw_zero two) (fact_zero zero)) (.eqRefl _)) (congrMul (.eqRefl _) (pw_zero _))).eqTrans (by ipra_ring)
  exact bound_congr e radius (.eqRefl _) raw

theorem product_at (p z B A a b : PTm n) : Γ ⊢[PRAAx]
    ap2 productF p (productData z B (pw a A) (pw b A)) ≐ qmul
      (ap2 powerF (query p z B A a b) (powerData z B (pw a A) (pw b A)))
      (ap2 decayF (query p z B A a b) (decayData (pw a A) (pw b A))) :=
  (GaussianNameArithmetic.multiply_at powerF decayF _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem product_bound (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (ap2 productF t (productData z B (pw a A) (pw b A)))
      (S A b*unit t+productCost A a b) (T A a*unit t) := by
  let s := query t z B A a b
  let U := unit s
  let V := unit t
  have hT := GaussianPolynomialPerturbation.power_positive (Γ := Γ) a (pred A) h.andE₂.andE₁.andE₁
  have hU := unit_positive (Γ := Γ) s
  have hV := unit_positive (Γ := Γ) t
  have grow : Γ ⊢[PRAAx] le V U := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have time := GaussianHarmonicLogarithmPower.power_source a b A h.andE₂.andE₁
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ hT hU) hU
    (GaussianEulerLowerTransformedPower.original_power_bound s z R B A a b h) (decay_bound _ _ s time.andE₁ time.andE₂)
  have oneStep : Γ ⊢[PRAAx] le V (U*U) := le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono grow hU)
  have middle := add_le_add₂ (mul_le_mul_right ((two*S A b+T A a)*U) grow) (mul_le_mul_right (two*T A a) oneStep)
  have full := add_le_add_right (S A b*V*(T A a*U*U)) (mul_le_mul_right (T A a) middle)
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ hT hU) hU)
    (GaussianRationalHorner.positive_product _ _ hT hV) _ (bound_congr (product_at t z B A a b).eqSymm (.eqRefl _) (.eqRefl _) raw)
  exact le_congr (by dsimp only [S,T,U,V]; ipra_ring) (by dsimp only [productCost,S,T,U,V]; ipra_ring) full

theorem original_sample_slack (p t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (observation p z B A a b) (S A b*unit p+T A a) (T A a*unit p) (cost A a b) t := by
  let U := unit p
  let V := unit t
  have hT := GaussianPolynomialPerturbation.power_positive (Γ := Γ) a (pred A) h.andE₂.andE₁.andE₁
  have hV := unit_positive (Γ := Γ) t
  have hU := unit_positive (Γ := Γ) p
  have old := GaussianEulerIntegrandName.original_power_times_decay z B _ _ (GaussianEulerLowerTransformedPower.old_source z R B A a b h)
  have near := distance_symmetric _ _ _ _ (GaussianRationalHorner.positive_product _ _ hV hU)
    (GaussianNameEquivalence.cross_at _ _ _ _ t p old)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ hT hV) (GaussianRationalHorner.positive_product _ _ hV hU)
    (product_bound t z R B A a b h) near
  have e := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) (ap2 productF t (productData z B (pw a A) (pw b A))) (observation p z B A a b)
    (GaussianRadiusExponentialName.sample_canonical GaussianEulerIntegrandName.exponentF (GaussianEulerIntegrandName.radius z B (pw a A) (pw b A)) p
      (GaussianEulerIntegrandName.exponentData z B (pw a A) (pw b A)))
  have growth : Γ ⊢[PRAAx] le (cost A a b) (cost A a b*T A a) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (cost A a b)) hT)
  have big := add_le_add_right ((S A b*U+T A a)*V*(T A a*V*(V*U)))
    (mul_le_mul_right (T A a*U*U*V*V) growth)
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ hT hV) (GaussianRationalHorner.positive_product _ _ hV hU))
    (GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ hT hU) hV) _
    (bound_congr e (.eqRefl _) (.eqRefl _) sum)
  exact le_congr (by dsimp only [cost,productCost,S,T,U,V,unit]; ipra_ring) (by dsimp only [cost,productCost,S,T,U,V,unit]; ipra_ring) big

theorem original_integrand_bound (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data z B (pw a A) (pw b A)))
      (pw b (pred A)*unit p+pw a (pred A)) (pw a (pred A)*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost A a b)
    (GaussianRationalHorner.positive_product _ _ (GaussianPolynomialPerturbation.power_positive a (pred A) h.andE₂.andE₁.andE₁) (unit_positive p))
    (original_sample_slack p (GaussianRationalSlackRemoval.precision (observation p z B A a b) (S A b*unit p+T A a) (T A a*unit p) (cost A a b)) z R B A a b h)

theorem original_lower_tail_transformed_integrand_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 3) (pw (var 5) (var 4)) (pw (var 6) (var 4))))
        (pw (var 6) (pred (var 4))*unit (var 0)+pw (var 5) (pred (var 4))) (pw (var 5) (pred (var 4))*unit (var 0))) :=
  closeUniv 7 (.impI (original_integrand_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTransformedIntegrand
