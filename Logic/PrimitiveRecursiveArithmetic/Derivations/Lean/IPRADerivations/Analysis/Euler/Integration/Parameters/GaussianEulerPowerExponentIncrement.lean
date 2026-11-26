import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmIncrement
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# Linear increment of the original Euler power exponent

The unchanged exponent of `t^(z-1)` samples its logarithm on the
original multiplication clock. Its increment at `t=a/b` and
`h=c/b` is compared to the exact Gaussian rational linear term
`(z/B-1)*c/a`. The two actual observation errors are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerExponentIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerClock power_exponent_at coefficient_bound)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qsub distanceBounded)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def exponentSample (p z B a b : PTm n) : PTm n := ap2 powerExponentF p (powerExponentData z B a b)
def increment (p q z B a b c : PTm n) : PTm n := qsub (exponentSample p z B (a+c) b) (exponentSample q z B a b)
def linear (z B a c : PTm n) : PTm n := qmul (coefficient z B) (fraction c a)
@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z B a c : PTm n) :
    Syn.subst σ (linear z B a c) = linear (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ c) :=
  by simp [linear]
def errorNumerator (p q R a c : PTm n) : PTm n :=
  (R+one)*GaussianPositiveRationalLogarithmIncrement.errorNumerator p q a c
abbrev errorDenominator := @GaussianPositiveRationalLogarithmIncrement.errorDenominator

theorem clock_later (p z B a b : PTm n) : Γ ⊢[PRAAx] le p (powerClock p z B a b) :=
  le_add_right _ _

theorem increment_at (p q z B a b c : PTm n) :
    Γ ⊢[PRAAx] increment p q z B a b c ≐
      qmul (coefficient z B) (GaussianPositiveRationalLogarithmIncrement.increment
        (powerClock p z B (a+c) b) (powerClock q z B a b) a b c) :=
  (qsub_congr (power_exponent_at p z B (a+c) b) (power_exponent_at q z B a b)).eqTrans
    (multiplication_difference _ _ _)

private theorem logarithm_retimed (p q z B a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (GaussianPositiveRationalLogarithmIncrement.increment
      (powerClock p z B (a+c) b) (powerClock q z B a b) a b c) (fraction c a)
      (GaussianPositiveRationalLogarithmIncrement.errorNumerator p q a c) (errorDenominator p q a) := by
  let s := powerClock p z B (a+c) b
  let t := powerClock q z B a b
  let P := unit p
  let Q := unit q
  let U := unit s
  let V := unit t
  let A := a*a
  have ha2 := positive_product a a ha ha
  have first : Γ ⊢[PRAAx] le P U := GaussianExponentialReference.unit_monotone (clock_later p z B (a+c) b)
  have second : Γ ⊢[PRAAx] le Q V := GaussianExponentialReference.unit_monotone (clock_later q z B a b)
  have compare : Γ ⊢[PRAAx] le
      (GaussianPositiveRationalLogarithmIncrement.errorNumerator s t a c*errorDenominator p q a)
      (GaussianPositiveRationalLogarithmIncrement.errorNumerator p q a c*errorDenominator s t a) := by
    change Γ ⊢[PRAAx] le (((c*c)*(U*V)+(U+V)*A)*(A*(P*Q))) (((c*c)*(P*Q)+(P+Q)*A)*(A*(U*V)))
    ipra_le (𝔞 A*𝔞 A*𝔞 V*𝔞 Q)*sl first+(𝔞 A*𝔞 A*𝔞 U*𝔞 P)*sl second
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ ha2 (positive_product _ _ (unit_positive s) (unit_positive t)))
    (positive_product _ _ ha2 (positive_product _ _ (unit_positive p) (unit_positive q))) compare
    (GaussianPositiveRationalLogarithmIncrement.original_increment s t a b c ha hb)

theorem exponent_increment (p q z R B a b c : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (increment p q z B a b c) (linear z B a c)
      (errorNumerator p q R a c) (errorDenominator p q a) := by
  let U := GaussianPositiveRationalLogarithmIncrement.errorNumerator p q a c
  let V := errorDenominator p q a
  let X := coefficient z B
  let Y := GaussianPositiveRationalLogarithmIncrement.increment (powerClock p z B (a+c) b)
    (powerClock q z B a b) a b c
  let Z := fraction c a
  have hV : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ (positive_product _ _ ha ha) (positive_product _ _ (unit_positive p) (unit_positive q))
  have weighted := GaussianRationalReciprocal.bounded_product X (qsub Y Z) (R+one) one U V
    (le_refl _) hV (coefficient_bound z R B hB hz) (logarithm_retimed p q z B a b c ha hb)
  have compare : Γ ⊢[PRAAx] distanceBounded (qmul X Y) (qmul X Z) (errorNumerator p q R a c) V :=
    GaussianRationalReciprocal.bound_congr (multiplication_difference X Y Z).eqSymm
      (.eqRefl _) (by ipra_ring) weighted
  exact distance_congr (increment_at p q z B a b c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) compare

theorem linear_bound (z R B a c : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] bounded (linear z B a c) ((R+one)*c) a := by
  have frac : Γ ⊢[PRAAx] bounded (fraction c a) c a :=
    GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point c a ha).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded c a ha)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl _) ha (coefficient_bound z R B hB hz) frac)

theorem original_Euler_power_exponent_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 4) ⋏ ComplexLogarithmRemainder.bounded (var 2) (var 3*var 4)) ⟶
      (le one (var 5) ⋏ le one (var 6)) ⟶
      distanceBounded (increment (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7))
        (linear (var 2) (var 4) (var 5) (var 7))
        (errorNumerator (var 0) (var 1) (var 3) (var 5) (var 7)) (errorDenominator (var 0) (var 1) (var 5))) :=
  closeUniv 8 (.impI (.impI (exponent_increment _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerExponentIncrement
