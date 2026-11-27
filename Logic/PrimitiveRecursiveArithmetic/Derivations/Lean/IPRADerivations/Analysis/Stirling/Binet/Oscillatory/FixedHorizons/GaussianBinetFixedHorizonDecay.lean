import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDecay
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceScalarMajorant
import IPRADerivations.Analysis.Euler.Integration.Decay.Increments.GaussianEulerDecayAddition
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# Actual damping at an independently chosen horizon

If the real decay exponent at the endpoint is at least the integer L,
split off the original integer decay and a nonnegative residual
exponent. Their product gives a dyadic bound whose horizon is
independent of the represented denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonDecay

open_ipra
open GaussianBinetLaplaceExponential (nameF data)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bounded_sum bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

private theorem observation_congr (p : PTm n) {a a' b b' : PTm n}
    (aEq : Γ ⊢[PRAAx] a ≐ a') (bEq : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] observation a b p ≐ observation a' b' p := by
  simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,p]) (σ' := ![a',b',p]) (fun j => by fin_cases j; exact aEq; exact bEq; exact .eqRefl p)

theorem real_decay (p a B L : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hcut : Γ ⊢[PRAAx] le (L*B) a) (hL : Γ ⊢[PRAAx] le L p) :
    Γ ⊢[PRAAx] bounded (observation a B p) (num 8) (unit L) := by
  let P := unit p
  let V := unit L
  let c := monus a (L*B)
  let x := decayData L one
  let y := decayData c B
  let r := GaussianFastValueCut.exponent (multiplyModulus decayF decayF x y) p
  let W := ap2 (multiplyF decayF decayF) p (multiplyData decayF decayF x y)
  let w := observation a B p
  have hP := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) L
  have hR := unit_positive (Γ := Γ) r
  have hpr : Γ ⊢[PRAAx] le p r := le_add_right _ _
  have hvr := GaussianExponentialReference.unit_monotone (le_trans hL hpr)
  have hvp := GaussianExponentialReference.unit_monotone hL
  have aEq : Γ ⊢[PRAAx] L*B+c*one ≐ a := by
    have eq : Γ ⊢[PRAAx] a ≐ L*B+c := eq_add_of_le hcut
    exact (congrAdd (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] c*one ≐ c)).eqTrans eq.eqSymm
  have cut := GaussianEulerDecayAddition.original_decay_add L one c B (le_refl one) hB
  have eq : Γ ⊢[PRAAx] observation (L*B+c*one) (one*B) p ≐ w := observation_congr p aEq (one_mul _)
  have near : Γ ⊢[PRAAx] distanceBounded w W two V :=
    distance_radius_mono _ _ (P+P) (P*P) two V (positive_product _ _ hP hP) hV
      (by dsimp only [V,P]; ipra_le 2*𝔞(unit p)*sl hvp)
      (distance_symmetric _ _ _ _ (positive_product _ _ hP hP)
        (distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ p p cut)))
  have shrink : Γ ⊢[PRAAx] bounded (observation L one r) (num 3) V :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV hR) hV
      (by dsimp only [V]; ipra_le 2*𝔞(unit L)*sl hvr) (GaussianEulerDecayFactorBounds.original_integer_decay_bound L r)
  have rem : Γ ⊢[PRAAx] bounded (observation c B r) two one :=
    bounded_radius_mono _ _ _ _ _ hR (le_refl one) (by ipra_le sl hR)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound r c B hB)
  have actual : Γ ⊢[PRAAx] W ≐ qmul (observation L one r) (observation c B r) :=
    (multiply_at decayF decayF x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have hw : Γ ⊢[PRAAx] bounded W (num 6) V :=
    bound_congr actual.eqSymm (by ipra_ring) (by dsimp only [V]; ipra_ring)
      (bounded_product _ _ (num 3) V two one hV (le_refl one) shrink rem)
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w :=
    GaussianRadiusExponentialName.sample_canonical _ _ p (decayPoint a B)
  have sum : Γ ⊢[PRAAx] bounded w (num 6*V+two*V) (V*V) :=
    bound_congr (GaussianRationalLinearProduct.add_sub_right W w can) (.eqRefl _) (.eqRefl _)
      (bounded_sum W (qsub w W) (num 6) V two V hV hV hw near)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV hV) hV
    (le_of_eq_add (d := zero) (by ipra_ring)) sum

theorem endpoint (p X Y D sign R T L : PTm n) (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hcut : Γ ⊢[PRAAx] le (L*D) (X*T)) (hL : Γ ⊢[PRAAx] le L p) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data X Y D sign R T T one)) (num 10) (unit L) := by
  let V := unit L
  let P := unit p
  have hV := unit_positive (Γ := Γ) L
  have hP := unit_positive (Γ := Γ) p
  have hD := positive_product (Γ := Γ) D one hz.andE₁.andE₂ (le_refl one)
  have hcut' : Γ ⊢[PRAAx] le (L*(D*one)) (X*T) := le_congr (by ipra_ring) (.eqRefl _) hcut
  have input : Γ ⊢[PRAAx] GaussianBinetLaplaceIntegrand.input X Y D sign R T T one :=
    .andI hz (.andI (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring)))
  have raw := GaussianBinetLaplaceDecay.observation_bound p X Y D sign R T T one (num 8) V input hV
    (real_decay p (X*T) (D*one) L hD hcut' hL)
  have grow := GaussianExponentialReference.unit_monotone hL
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV hP) hV
    (by dsimp only [V,P]; ipra_le 2*𝔞(unit L)*sl grow) raw

end LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonDecay
