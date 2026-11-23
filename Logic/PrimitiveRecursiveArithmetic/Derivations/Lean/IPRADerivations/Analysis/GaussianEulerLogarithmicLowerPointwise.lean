import IPRADerivations.Analysis.GaussianEulerLowerLogarithmPower
import IPRADerivations.Analysis.GaussianEulerLowerTransformedIntegrand
import IPRADerivations.Analysis.GaussianEulerLogarithmicCompactName
import IPRADerivations.Analysis.GaussianDescentClockArithmetic

/-!
# Original logarithmic Euler rows at transformed lower times

The original margin 1/A is retained. At time (a/b)^(2A), applying
the checked Euler bound to the squared root gives (b/a)^(2A-2).
The actual logarithmic power contributes j!(2A)^j b/a. Their product
therefore has the integrable original root-panel exponent 2A-1.
The original compact evaluator clock pays its own observation gain;
one finite gap removes only the auxiliary raw-row precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerPointwise

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def degree (A : PTm n) : PTm n := two*A
def exponent (A : PTm n) : PTm n := pred (degree A)
def coefficient (j A : PTm n) : PTm n := fact j*pw (degree A) j
def rawCost (j A a b : PTm n) : PTm n :=
  pw b (two*pred A)*GaussianEulerLowerLogarithmPower.gain j (degree A) a b+
    coefficient j A*b+GaussianEulerLowerLogarithmPower.gain j (degree A) a b
def observationCost (j R A E T a b : PTm n) : PTm n :=
  GaussianEulerLogarithmicMultiplier.observationCost j R E T+rawCost j A a b
def numerator (p j A a b : PTm n) : PTm n := coefficient j A*pw b (exponent A)*unit p+pw a (exponent A)
def denominator (p A a : PTm n) : PTm n := pw a (exponent A)*unit p
def source (z R B A E T a b : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerOrder.source z R B A a b ⋏
    (le one E ⋏ GaussianCompactLogarithmBounds.domain (pw a (degree A)) (pw b (degree A)) E T)

@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (degree A) = degree (Syn.subst σ A) := by simp [degree]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (exponent A) = exponent (Syn.subst σ A) := by simp [exponent]
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (j A : PTm n) :
    Syn.subst σ (coefficient j A) = coefficient (Syn.subst σ j) (Syn.subst σ A) := by simp [coefficient,fact]

theorem coefficient_positive (j A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (coefficient j A) :=
  positive_product _ _ (GaussianRationalPolynomialExponential.factorial_positive j)
    (GaussianPolynomialPerturbation.power_positive _ j
      (positive_product two A (le_succ_self one) hA))

theorem exponent_identity (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    exponent A ≐ succ (two*pred A) := by
  have eq : Γ ⊢[PRAAx] degree A ≐ succ (succ (two*pred A)) := by
    have e := natEq (RationalIntegerNormalization.positive_form (Γ := Γ) hA)
    apply deriveNat
    dsimp only [degree]
    ipra_simps
    rw [e]
    ring
  exact (congrPred eq).eqTrans (pred_succ _)

private theorem integrand_time_congr (p z B a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.sample p z B a b ≐ GaussianEulerIntegrandName.sample p z B c d := by
  simpa only [GaussianEulerIntegrandName.subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (GaussianEulerIntegrandName.sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,z,B,a,b]) (σ' := ![p,z,B,c,d])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact ha; exact hb)

theorem original_double_time_integrand (p z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerIntegrandName.sample p z B (pw a (degree A)) (pw b (degree A)))
      (pw b (two*pred A)*unit p+pw a (two*pred A)) (pw a (two*pred A)*unit p) := by
  have powers := GaussianHarmonicLogarithmPower.power_source a b two h.andE₂.andE₁
  have src := Prf.andI h.andE₁ (.andI powers (pw_le_pw two h.andE₂.andE₂))
  have old := GaussianEulerLowerTransformedIntegrand.original_integrand_bound p z R B A (pw a two) (pw b two) src
  have actual := (GaussianEulerIntegrandName.sample_at (Γ := Γ) p z B _ _).eqSymm.eqTrans
    (integrand_time_congr p z B _ _ _ _ (GaussianDescentClockArithmetic.power_composition a two A)
      (GaussianDescentClockArithmetic.power_composition b two A))
  exact bound_congr actual
    (congrAdd (congrMul (GaussianDescentClockArithmetic.power_composition b two (pred A)) (.eqRefl _))
      (GaussianDescentClockArithmetic.power_composition a two (pred A)))
    (congrMul (GaussianDescentClockArithmetic.power_composition a two (pred A)) (.eqRefl _)) old

theorem original_raw_bound (p j z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerLogarithmicMultiplier.sample p j z B (pw a (degree A)) (pw b (degree A)))
      (coefficient j A*pw b (exponent A)*unit p+rawCost j A a b*pw a (exponent A))
      (pw a (exponent A)*unit p) := by
  let U := pw a (two*pred A)
  let V := pw b (two*pred A)
  let P := unit p
  let C := coefficient j A
  let G := GaussianEulerLowerLogarithmPower.gain j (degree A) a b
  have hU := GaussianPolynomialPerturbation.power_positive (Γ := Γ) a (two*pred A) h.andE₂.andE₁.andE₁
  have hp := unit_positive (Γ := Γ) p
  have first := original_double_time_integrand p z R B A a b h
  have second := GaussianEulerLowerLogarithmPower.original_derivative_lower_logarithm_bound p j A a b h.andE₂.andE₁ h.andE₂.andE₂
  have raw := bounded_product _ _ _ _ _ _ (positive_product _ _ hU hp)
    (positive_product _ _ h.andE₂.andE₁.andE₁ hp) first second
  have compare : Γ ⊢[PRAAx] le ((V*P+U)*(C*b*P+G*a))
      ((C*(V*b)*P+rawCost j A a b*(U*a))*P) := by
    dsimp only [rawCost,V,C,G]
    ipra_le (𝔞(pw b (two*pred A))*𝔞(GaussianEulerLowerLogarithmPower.gain j (degree A) a b)*𝔞 a*𝔞 P)*sl hU+
      (𝔞 U*𝔞(coefficient j A)*𝔞 b*𝔞 P)*sl h.andE₂.andE₁.andE₁+
      (𝔞 U*𝔞(GaussianEulerLowerLogarithmPower.gain j (degree A) a b)*𝔞 a)*sl hp
  have norm : Γ ⊢[PRAAx] bounded (GaussianEulerLogarithmicMultiplier.sample p j z B (pw a (degree A)) (pw b (degree A)))
      (C*(V*b)*P+rawCost j A a b*(U*a)) ((U*a)*P) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hp) (positive_product _ _ h.andE₂.andE₁.andE₁ hp))
      (positive_product _ _ (positive_product _ _ hU h.andE₂.andE₁.andE₁) hp)
      (le_congr (.eqRefl _)
        (by dsimp only [U,V,P,C,G,coefficient,degree]; try ipra_ring) (mul_le_mul_right ((U*a)*P) compare)) raw
  have powerA := (pw_succ a (two*pred A)).eqSymm.eqTrans
    (congrAp2 powF (exponent_identity A h.andE₁.andE₁).eqSymm (.eqRefl a))
  have powerB := (pw_succ b (two*pred A)).eqSymm.eqTrans
    (congrAp2 powF (exponent_identity A h.andE₁.andE₁).eqSymm (.eqRefl b))
  exact bound_congr (.eqRefl _) (congrAdd (congrMul (congrMul (.eqRefl C) powerB) (.eqRefl P))
    (congrMul (.eqRefl _) powerA)) (congrMul powerA (.eqRefl P)) norm

theorem compact_source (z R B A E T a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A E T a b) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicMultiplier.source z R B E T (pw a (degree A)) (pw b (degree A)) :=
  .andI (.andI h.andE₁.andE₁.andE₂.andE₁.andE₁ (.andI h.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁.andE₂)) h.andE₂.andE₂

theorem observation_clock_budget (H P Q S : PTm n) (h : Γ ⊢[PRAAx] le (H*P) Q) : Γ ⊢[PRAAx]
    le ((H*(Q+S))*(P*S)) ((S+H*P)*(Q*S)) := by ipra_le (𝔞 S*𝔞 S)*sl h

theorem original_observation_slack (p s j z R B A E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A E T a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (GaussianEulerLogarithmicCompactName.sample p j R E T z B (pw a (degree A)) (pw b (degree A)))
      (numerator p j A a b) (denominator p A a) (observationCost j R A E T a b) s := by
  let H := GaussianEulerLogarithmicMultiplier.observationCost j R E T
  let r := GaussianEulerLogarithmicCompactName.query p j R E T
  let P := unit p
  let Q := unit r
  let S := unit s
  let V := pw a (exponent A)
  have hc := compact_source z R B A E T a b h
  have same : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T
      (pw a (degree A)) (pw b (degree A)) (pw a (degree A)) (pw b (degree A)) zero one :=
    .andI hc.andE₁ (.andI hc.andE₂ (.andI hc.andE₂ (.andI (le_refl one)
      (GaussianRationalPowerDifference.distance_refl_zero _ one (le_refl one)))))
  have old := GaussianEulerLogarithmicMultiplier.original_variation r s j z R B E T _ _ _ _ zero one same
  have old' : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (GaussianEulerLogarithmicCompactName.sample p j R E T z B (pw a (degree A)) (pw b (degree A)))
      (GaussianEulerLogarithmicMultiplier.sample s j z B (pw a (degree A)) (pw b (degree A))) (H*(Q+S)) (Q*S) :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold GaussianEulerLogarithmicMultiplier.numerator; dsimp only [H,Q,S]; ipra_ring)
      (by unfold GaussianNamedInverseRate.rateDenominator; dsimp only [Q,S]; ipra_ring) old
  have near : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (GaussianEulerLogarithmicCompactName.sample p j R E T z B (pw a (degree A)) (pw b (degree A)))
      (GaussianEulerLogarithmicMultiplier.sample s j z B (pw a (degree A)) (pw b (degree A))) (S+H*P) (P*S) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (positive_product _ _ (unit_positive r) (unit_positive s)) (positive_product _ _ (unit_positive p) (unit_positive s))
      (observation_clock_budget H P Q S (GaussianEulerLogarithmicCompactName.query_budget p j R E T)) old'
  have hV := GaussianPolynomialPerturbation.power_positive (Γ := Γ) a (exponent A) h.andE₁.andE₂.andE₁.andE₁
  have raw := original_raw_bound s j z R B A a b h.andE₁
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive s)) (positive_product _ _ hV (unit_positive s)) near raw
  exact bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive s)) (positive_product _ _ hV (unit_positive s)))
    (positive_product _ _ (positive_product _ _ hV (unit_positive p)) (unit_positive s))
    (le_of_eq_add (d := zero) (by unfold numerator denominator observationCost; dsimp only [H,P,Q,S,V]; unfold unit; ipra_ring)) joined

theorem original_lower_pointwise (p j z R B A E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A E T a b) : Γ ⊢[PRAAx]
    bounded (GaussianEulerLogarithmicCompactName.sample p j R E T z B (pw a (degree A)) (pw b (degree A)))
      (numerator p j A a b) (denominator p A a) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (observationCost j R A E T a b)
    (positive_product _ _ (GaussianPolynomialPerturbation.power_positive a (exponent A) h.andE₁.andE₂.andE₁.andE₁) (unit_positive p))
    (original_observation_slack p _ j z R B A E T a b h)

theorem original_logarithmic_Euler_lower_pointwise_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      bounded (GaussianEulerLogarithmicCompactName.sample (var 0) (var 1) (var 3) (var 6) (var 7) (var 2) (var 4)
        (pw (var 8) (degree (var 5))) (pw (var 9) (degree (var 5))))
        (numerator (var 0) (var 1) (var 5) (var 8) (var 9)) (denominator (var 0) (var 5) (var 8))) :=
  closeUniv 10 (.impI (original_lower_pointwise _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerPointwise
