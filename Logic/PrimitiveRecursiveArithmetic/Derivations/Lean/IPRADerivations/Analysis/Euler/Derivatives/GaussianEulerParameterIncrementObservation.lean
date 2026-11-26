import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianEulerLogarithmicParameterIncrement
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerParameterExponentialIncrement

/-!
# Original parameter-increment observations at the compact unit radius

The original increment name has radius one from source compact guards
and the actual small increment. Its unchanged exponential observation
is compared with the actual constant exponential of the old logarithm
observation. Both true nested clocks are retained. Original exponential
addition then supplies an explicit diagonal comparison with the perturbed
Euler observation, without a Taylor-error premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerParameterIncrementObservation

open_ipra
open GaussianEulerLogarithmicParameterIncrement (source increment)
open GaussianEulerParameterExponentialIncrement (shifted incrementF incrementData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianRationalHorner (qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (p h D a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF GaussianPositiveRationalLogarithm.logF
    (ofGaussian h D) (GaussianPositiveRationalLogarithm.data a b)) p
def unitData (h D a b : PTm n) : PTm n := GaussianRadiusExponentialName.data one (incrementData h D a b)
def unitF : PR 2 := GaussianRadiusExponentialName.nameF incrementF
def unitProductF : PR 2 := multiplyF GaussianEulerIntegrandName.nameF unitF
def unitProductData (z B h D a b : PTm n) : PTm n := multiplyData GaussianEulerIntegrandName.nameF unitF
  (GaussianEulerIntegrandName.data z B a b) (unitData h D a b)
def productCost (z B h D a b : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyModulus GaussianEulerIntegrandName.nameF unitF
    (GaussianEulerIntegrandName.data z B a b) (unitData h D a b)+num 3

def modelCost (z R B E T h D a b : PTm n) : PTm n := productCost z B h D a b+num 6*GaussianEulerLogarithmicMultiplier.eulerMajorant R E T

ipra_subst clock
ipra_subst unitData
ipra_subst unitProductData

theorem increment_at (p h D a b : PTm n) : Γ ⊢[PRAAx]
    ap2 incrementF p (incrementData h D a b) ≐ increment (clock p h D a b) h D a b :=
  (GaussianNameArithmetic.multiply_at constantF GaussianPositiveRationalLogarithm.logF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem parameter_unit_bound (z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx] bounded (ofGaussian h D) one one := by
  have positive : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicMultiplier.logRadius E T) :=
    le_of_eq_add (d := E*(T+one)+num 24) (by unfold GaussianEulerLogarithmicMultiplier.logRadius GaussianCompactLogarithmBounds.radius; ipra_ring)
  have small : Γ ⊢[PRAAx] le X Y := le_trans
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right X positive)) hs.andE₂.andE₂.andE₂.andE₁
  exact bounded_radius_mono _ _ _ _ _ hs.andE₂.andE₂.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) small) hs.andE₂.andE₂.andE₂.andE₂

theorem increment_unit_bound (p z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx] bounded (increment p h D a b) one one :=
  bounded_radius_mono _ _ _ _ _ hs.andE₂.andE₂.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hs.andE₂.andE₂.andE₂.andE₁)
    (GaussianEulerLogarithmicParameterIncrement.original_increment_bound p z R B E T a b h D X Y hs)

theorem unit_input (z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input incrementF one (incrementData h D a b) := by
  refine .andI (GaussianEulerParameterExponentialIncrement.increment_regular h D a b hs.andE₁.andE₂.andE₁) (.allI ?_)
  have shiftedSource : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift h) (Syn.shift D) (Syn.shift X) (Syn.shift Y) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have raw := bound_congr (increment_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift h) (Syn.shift D) (Syn.shift a) (Syn.shift b)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (increment_unit_bound (clock (var 0) (Syn.shift h) (Syn.shift D) (Syn.shift a) (Syn.shift b))
      (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b)
      (Syn.shift h) (Syn.shift D) (Syn.shift X) (Syn.shift Y) shiftedSource)
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerParameterExponentialIncrement.subst_incrementData,
    Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using raw

/-- The actual nested product and exponential input clocks are both later
than the fixed original logarithm query p. -/
theorem logarithm_query_later (p h D a b : PTm n) : Γ ⊢[PRAAx]
    le p (clock (GaussianRadiusExponentialName.inputPrecision one p) h D a b) :=
  le_trans (GaussianRadiusExponentialLipschitzRate.original_clock_later one p) (le_add_right _ _)

theorem increment_query_error (p z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 incrementF (GaussianRadiusExponentialName.inputPrecision one p) (incrementData h D a b))
      (increment p h D a b) two (unit p) := by
  let r := clock (GaussianRadiusExponentialName.inputPrecision one p) h D a b
  have regular := GaussianPositiveRationalLogarithm.name_regular a b hs.andE₁.andE₂.andE₁
  have old := GaussianNameEquivalence.point_at GaussianPositiveRationalLogarithm.logF (GaussianPositiveRationalLogarithm.data a b) r p regular
  have later := GaussianExponentialReference.unit_monotone (Γ := Γ) (logarithm_query_later p h D a b)
  have logs := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive r) (unit_positive p)) (unit_positive p)
    (by ipra_le 𝔞(unit p)*sl later) old
  have scaled := bounded_product _ _ _ _ _ _ (le_refl one) (unit_positive p)
    (parameter_unit_bound z R B E T a b h D X Y hs) logs
  exact bound_congr ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm.eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (increment_at _ h D a b).eqSymm (.eqRefl _)))
    (by ipra_ring) (by ipra_ring) scaled

/-- The original scalar-sum program uses the same actual radius-one cutoff
on both sides. Its genuine uniform finite Lipschitz bound pays six errors. -/
theorem exponential_query_error (p z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 unitF p (unitData h D a b))
      (GaussianRadiusExponentialName.sample constantF one p (increment p h D a b)) (num 6) (unit p) := by
  let r := GaussianRadiusExponentialName.inputPrecision one p
  let k := GaussianRadiusExponentialName.index one p
  have finite := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz
    (ap2 incrementF r (incrementData h D a b)) (increment p h D a b) one two (unit p) k (unit_positive p)
    (GaussianRadiusExponentialName.query_bound incrementF one (incrementData h D a b) p (unit_input z R B E T a b h D X Y hs))
    (increment_unit_bound p z R B E T a b h D X Y hs) (increment_query_error p z R B E T a b h D X Y hs)
  have first := GaussianRadiusExponentialName.sample_at (Γ := Γ) incrementF one p (incrementData h D a b)
  have last := (GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF one p (increment p h D a b)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (constant_at r (increment p h D a b)))
  exact distance_congr first.eqSymm last.eqSymm
    ((congrMul (pw_one (num 3)) (.eqRefl _)).eqTrans (by ipra_ring)) (.eqRefl _) finite

theorem original_unit_product (z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerIntegrandName.nameF unitProductF
      (GaussianEulerIntegrandName.data (shifted z B h D) (B*D) a b) (unitProductData z B h D a b) := by
  have time := hs.andE₁.andE₂.andE₁
  have euler := GaussianEulerIntegrandName.name_regular z B a b (.andI hs.andE₁.andE₁.andE₁ time)
  have normal := GaussianEulerParameterExponentialIncrement.increment_input h D a b time
  have unitInput := unit_input z R B E T a b h D X Y hs
  have change := GaussianExponentialRadiusIndependence.same_input_cross incrementF _ one (incrementData h D a b) normal unitInput
  have actual := GaussianGammaAdjacentCutoff.multiply_cross GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
    GaussianEulerParameterExponentialIncrement.exponentialF unitF (GaussianEulerIntegrandName.data z B a b)
    (GaussianEulerIntegrandName.data z B a b) (GaussianEulerParameterExponentialIncrement.exponentialData h D a b) (unitData h D a b)
    euler euler (GaussianEulerParameterExponentialIncrement.exponential_regular h D a b time)
    (GaussianRadiusExponentialName.name_regular _ _ _ unitInput) (cross_refl _ _ euler) change
  exact cross_trans _ _ _ _ _ _
    (GaussianEulerParameterExponentialIncrement.original_integrand_product z B h D a b (.andI hs.andE₁.andE₁.andE₁ time) hs.andE₂.andE₁) actual

theorem original_parameter_increment_exponential_query_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⟶
      distanceBounded (ap2 unitF (var 0) (unitData (var 8) (var 9) (var 6) (var 7)))
        (GaussianRadiusExponentialName.sample constantF one (var 0) (increment (var 0) (var 8) (var 9) (var 6) (var 7)))
        (num 6) (unit (var 0))) :=
  closeUniv 12 (.impI (exponential_query_error _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerParameterIncrementObservation
