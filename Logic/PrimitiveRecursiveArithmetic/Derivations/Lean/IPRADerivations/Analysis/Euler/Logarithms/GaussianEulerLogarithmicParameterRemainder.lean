import IPRADerivations.Analysis.Euler.GaussianEulerParameterIncrementObservation
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicClientRate

/-!
# Pointwise parameter Taylor error for the original logarithmic evaluator

The actual perturbed parameter is (D*z+B*h)/(B*D). Both native compact
disks are source guards. An actual finite exponential increment, its
proved quadratic tail and the exact numerical order successor derive
the remainder. Original independently retimed logarithmic observations
are compared with one raw anchor. One finite rational gap removes only
auxiliary anchor errors and retains the three requested observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerParameterIncrementObservation (unitF unitData unitProductF unitProductData productCost modelCost)
open GaussianEulerLogarithmicParameterIncrement (increment linearModel curvature)
open GaussianEulerLogarithmicMultiplier (majorant logRadius observationCost)
open GaussianRationalHorner (qadd qmul ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z R S B E T a b h D X Y : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicParameterIncrement.source z R B E T a b h D X Y ⋏
    GaussianEulerLogarithmicMultiplier.source (shifted z B h D) S (B*D) E T a b

def actualLinear (q r j z R B E T a b h D : PTm n) : PTm n :=
  qadd (GaussianEulerLogarithmicCompactName.sample q j R E T z B a b)
    (qmul (ofGaussian h D) (GaussianEulerLogarithmicCompactName.sample r (succ j) R E T z B a b))
def gain (j z R B E T a b h D : PTm n) : PTm n := pw (logRadius E T) j*modelCost z R B E T h D a b

def numerator (p q r j R E T X Y : PTm n) : PTm n :=
  curvature j R E T*X*X*(unit p*unit q*unit r)+(unit q*unit r+unit p*unit r+unit p*unit q)*(Y*Y)
def denominator (p q r Y : PTm n) : PTm n := (Y*Y)*(unit p*unit q*unit r)
def auxiliaryCost (j z R S B E T a b h D : PTm n) : PTm n :=
  gain j z R B E T a b h D+observationCost j S E T+observationCost j R E T+observationCost (succ j) R E T

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z R S B E T a b h D X Y : PTm n) :
    (input z R S B E T a b h D X Y).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ S)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ X) (Syn.subst σ Y) := by simp [input]

private theorem multiply_distance (c u v M A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] GaussianRationalMetric.bounded c M one) (hd : Γ ⊢[PRAAx] distanceBounded u v A D) : Γ ⊢[PRAAx]
    distanceBounded (qmul c u) (qmul c v) (M*A) D :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) hD hc hd)

private theorem multiply_right_distance (u v c M A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] GaussianRationalMetric.bounded c M one) (hd : Γ ⊢[PRAAx] distanceBounded u v A D) : Γ ⊢[PRAAx]
    distanceBounded (qmul u c) (qmul v c) (M*A) D :=
  distance_congr (GaussianRationalPowerAlgebra.qmul_commutative c u) (GaussianRationalPowerAlgebra.qmul_commutative c v)
    (.eqRefl _) (.eqRefl _) (multiply_distance c u v M A D hD hc hd)

theorem original_unit_product_observation (s z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerLogarithmicParameterIncrement.source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrandName.sample s (shifted z B h D) (B*D) a b)
      (qmul (GaussianEulerIntegrandName.sample s z B a b) (ap2 unitF s (unitData h D a b)))
      (productCost z B h D a b) (unit s) := by
  have up := unit_positive (Γ := Γ) s
  have old := GaussianNameEquivalence.diagonal_at _ _ _ _ s
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (GaussianEulerParameterIncrementObservation.original_unit_product z R B E T a b h D X Y hs))
  have near := GaussianNameRingLaws.multiply_sample_error GaussianEulerIntegrandName.nameF unitF
    (GaussianEulerIntegrandName.data z B a b) (unitData h D a b) s
    (GaussianEulerIntegrandName.name_regular z B a b (.andI hs.andE₁.andE₁.andE₁ hs.andE₁.andE₂.andE₁))
    (GaussianRadiusExponentialName.name_regular _ _ _ (GaussianEulerParameterIncrementObservation.unit_input z R B E T a b h D X Y hs))
  exact distance_congr (GaussianEulerIntegrandName.sample_at s _ _ _ _).eqSymm
    (GaussianRationalSyntheticDivision.qmul_congr (GaussianEulerIntegrandName.sample_at s z B a b).eqSymm (.eqRefl _))
    (by unfold productCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ up old near)

theorem original_frozen_model_error (s z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerLogarithmicParameterIncrement.source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrandName.sample s (shifted z B h D) (B*D) a b)
      (qmul (GaussianEulerIntegrandName.sample s z B a b)
        (GaussianRadiusExponentialName.sample GaussianGammaCanonicalExponent.constantF one s (increment s h D a b)))
      (modelCost z R B E T h D a b) (unit s) := by
  have near := multiply_distance _ _ _ (GaussianEulerLogarithmicMultiplier.eulerMajorant R E T) _ _ (unit_positive s)
    (GaussianEulerLogarithmicMultiplier.euler_bound s z R B E T a b hs.andE₁)
    (GaussianEulerParameterIncrementObservation.exponential_query_error s z R B E T a b h D X Y hs)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold modelCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive s)
      (original_unit_product_observation s z R B E T a b h D X Y hs) near)

theorem original_raw_remainder (s j z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerLogarithmicParameterIncrement.source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerLogarithmicMultiplier.sample s j (shifted z B h D) (B*D) a b)
      (linearModel s j z B h D a b)
      (curvature j R E T*X*X*unit s+gain j z R B E T a b h D*(Y*Y)) ((Y*Y)*unit s) := by
  let P := GaussianEulerLogarithmicMultiplier.logarithmicPower s j a b
  let V := GaussianRadiusExponentialName.sample GaussianGammaCanonicalExponent.constantF one s (increment s h D a b)
  let U := GaussianEulerIntegrandName.sample s z B a b
  have hp := unit_positive (Γ := Γ) s
  have yy := positive_product _ _ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₁
  have den := positive_product _ _ yy hp
  have scaled := multiply_right_distance _ _ P (pw (logRadius E T) j) _ _ hp
    (GaussianEulerLogarithmicMultiplier.logarithmic_power_bound s j a b E T hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₂)
    (original_frozen_model_error s z R B E T a b h D X Y hs)
  have shuffled : Γ ⊢[PRAAx] qmul (qmul U V) P ≐ qmul (qmul U P) V :=
    (GaussianReciprocalHorner.qmul_associative U V P).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative V P)).eqTrans
        (GaussianReciprocalHorner.qmul_associative U P V).eqSymm)
  have first : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicMultiplier.sample s j (shifted z B h D) (B*D) a b)
      (qmul (GaussianEulerLogarithmicMultiplier.sample s j z B a b) V)
      (gain j z R B E T a b h D*(Y*Y)) ((Y*Y)*unit s) :=
    distance_radius_mono _ _ _ _ _ _ hp den (le_of_eq_add (d := zero) (by unfold gain; ipra_ring))
      (distance_congr (.eqRefl _) shuffled (.eqRefl _) (.eqRefl _) scaled)
  have second := distance_radius_mono _ _ _ _ (curvature j R E T*X*X*unit s) ((Y*Y)*unit s) yy den
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianEulerLogarithmicParameterIncrement.original_constant_exponential_remainder s s j z R B E T a b h D X Y hs)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first second)

theorem original_linear_anchor_error (q r s j z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerLogarithmicParameterIncrement.source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (actualLinear q r j z R B E T a b h D) (linearModel s j z B h D a b)
      (unit r*unit s+unit q*unit s+(observationCost j R E T+observationCost (succ j) R E T)*(unit q*unit r))
      (unit q*unit r*unit s) := by
  have hq := unit_positive (Γ := Γ) q
  have hr := unit_positive (Γ := Γ) r
  have hs' := unit_positive (Γ := Γ) s
  have qs := positive_product _ _ hq hs'
  have rs := positive_product _ _ hr hs'
  have den := positive_product _ _ (positive_product _ _ hq hr) hs'
  have first := distance_radius_mono _ _ _ _ ((unit s+observationCost j R E T*unit q)*unit r) (unit q*unit r*unit s) qs den
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianEulerLogarithmicClientRate.original_to_raw q s j z R B E T a b hs.andE₁)
  have second := multiply_distance _ _ _ one _ _ rs
    (GaussianEulerParameterIncrementObservation.parameter_unit_bound z R B E T a b h D X Y hs)
    (GaussianEulerLogarithmicClientRate.original_to_raw r s (succ j) z R B E T a b hs.andE₁)
  have second' := distance_radius_mono _ _ _ _ ((unit s+observationCost (succ j) R E T*unit r)*unit q)
    (unit q*unit r*unit s) rs den (le_of_eq_add (d := zero) (by ipra_ring)) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ den first second')

theorem original_remainder_slack (p q r s j z R S B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] input z R S B E T a b h D X Y) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (GaussianEulerLogarithmicCompactName.sample p j S E T (shifted z B h D) (B*D) a b)
        (actualLinear q r j z R B E T a b h D)) (numerator p q r j R E T X Y) (denominator p q r Y)
      (auxiliaryCost j z R S B E T a b h D) s := by
  let P := unit p
  let Q := unit q
  let V := unit r
  let W := unit s
  let Y2 := Y*Y
  let DD := Y2*(P*Q*V)*W
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hr := unit_positive (Γ := Γ) r
  have hw := unit_positive (Γ := Γ) s
  have yy := positive_product _ _ hs.andE₁.andE₂.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₁
  have dpq := positive_product _ _ hp hq
  have dpqr := positive_product _ _ dpq hr
  have dd : Γ ⊢[PRAAx] le one DD := positive_product _ _ (positive_product _ _ yy dpqr) hw
  have left := distance_radius_mono _ _ _ _
    ((W+observationCost j S E T*P)*(Y2*Q*V)) DD (positive_product _ _ hp hw) dd
    (le_of_eq_add (d := zero) (by dsimp only [DD,P,Q,V,W,Y2]; ipra_ring))
    (GaussianEulerLogarithmicClientRate.original_to_raw p s j (shifted z B h D) S (B*D) E T a b hs.andE₂)
  have middle := distance_radius_mono _ _ _ _
    ((curvature j R E T*X*X*W+gain j z R B E T a b h D*Y2)*(P*Q*V)) DD
    (positive_product _ _ yy hw) dd (le_of_eq_add (d := zero) (by dsimp only [DD,P,Q,V,W,Y2]; ipra_ring))
    (original_raw_remainder s j z R B E T a b h D X Y hs.andE₁)
  have right := distance_symmetric _ _ _ _ dd
    (distance_radius_mono _ _ _ _
      ((V*W+Q*W+(observationCost j R E T+observationCost (succ j) R E T)*(Q*V))*(Y2*P)) DD
      (positive_product _ _ (positive_product _ _ hq hr) hw) dd
      (le_of_eq_add (d := zero) (by dsimp only [DD,P,Q,V,W,Y2]; ipra_ring))
      (original_linear_anchor_error q r s j z R B E T a b h D X Y hs.andE₁))
  exact bound_congr (.eqRefl _)
    (by unfold numerator denominator auxiliaryCost; dsimp only [P,Q,V,W,Y2]; unfold unit; ipra_ring)
    (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ dd left (distance_triangle_same _ _ _ _ _ _ dd middle right))

/-- The unchanged retimed Euler logarithmic clients retain their three
independent requested observation errors and a genuine quadratic term. -/
theorem original_parameter_remainder (p q r j z R S B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] input z R S B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerLogarithmicCompactName.sample p j S E T (shifted z B h D) (B*D) a b)
      (actualLinear q r j z R B E T a b h D) (numerator p q r j R E T X Y) (denominator p q r Y) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost j z R S B E T a b h D)
    (positive_product _ _ (positive_product _ _ hs.andE₁.andE₂.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₁)
      (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive r)))
    (original_remainder_slack p q r _ j z R S B E T a b h D X Y hs)

theorem original_all_orders_Euler_parameter_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (input (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      distanceBounded
        (GaussianEulerLogarithmicCompactName.sample (var 0) (var 3) (var 6) (var 8) (var 9)
          (shifted (var 4) (var 7) (var 12) (var 13)) (var 7*var 13) (var 10) (var 11))
        (actualLinear (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9) (var 14) (var 15))
        (denominator (var 0) (var 1) (var 2) (var 15))) :=
  closeUniv 16 (.impI (original_parameter_remainder _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterRemainder
