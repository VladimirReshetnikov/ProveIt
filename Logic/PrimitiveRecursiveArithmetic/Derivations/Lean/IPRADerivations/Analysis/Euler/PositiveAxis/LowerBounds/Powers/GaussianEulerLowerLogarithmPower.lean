import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianLogarithmFactorialPowerBound
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerLowerPowerRebasing
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaRecurrenceWeightName

/-!
# The original logarithmic power at a transformed lower time

For positive a<=b and every numerical m,j, the original observation of
log((a/b)^m)^j has norm at most j! m^j b/a plus its explicit power-query
gain times 2^-p. The actual log power name, reciprocal harmonic samples,
finite factorial-term comparison and original normalized powers are used
throughout. Setting m=2A gives exactly the lower logarithmic coefficient
from the integral-derivative tail estimate. No tail integral is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerLogarithmPower

open_ipra
open GaussianPositiveRationalLogarithm (source)
open GaussianHarmonicLogarithmName (sample)
open GaussianRationalReciprocal (power bounded_product bound_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def targetRadius (m a b : PTm n) : PTm n := GaussianPositiveRationalLogarithm.radius (pw a m) (pw b m)
def commonRadius (m a b : PTm n) : PTm n := targetRadius m a b+m*(b+one)
def gain (j m a b : PTm n) : PTm n := j*pw (commonRadius m a b) (pred j)
def rawPower (p j m a b : PTm n) : PTm n :=
  power (GaussianPositiveRationalLogarithm.sample p (pw a m) (pw b m)) j
def numerator (p j m a b : PTm n) : PTm n := fact j*pw m j*b*unit p+gain j m a b*a
def denominator (p a : PTm n) : PTm n := a*unit p
def auxiliaryCost (j m a b : PTm n) : PTm n := pw m j*GaussianUpperTimeLogarithmPower.gain j b+gain j m a b

ipra_subst targetRadius
ipra_subst commonRadius
ipra_subst gain
ipra_subst rawPower
ipra_subst numerator [fact]
ipra_subst denominator
ipra_subst auxiliaryCost

theorem harmonic_power_slack (p t j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (power (sample p a b) j)
      (GaussianLogarithmFactorialPowerBound.numerator p j a b)
      (GaussianLogarithmFactorialPowerBound.denominator p b) (two*GaussianUpperTimeLogarithmPower.gain j a) t := by
  have near := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p))
    (GaussianUpperTimeLogarithmPower.original_harmonic_power_distance t p j a b hs hba)
  have old := GaussianLogarithmFactorialPowerBound.original_power_bound t j a b hs hba
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ (unit_positive t) (unit_positive p))
    (positive_product _ _ hs.andE₂ (unit_positive t)) near old
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive t) (unit_positive p))
      (positive_product _ _ hs.andE₂ (unit_positive t)))
    (positive_product _ _ (positive_product _ _ hs.andE₂ (unit_positive p)) (unit_positive t)) _ joined
  exact le_of_eq_add (d := zero) (by
    unfold GaussianLogarithmFactorialPowerBound.numerator GaussianLogarithmFactorialPowerBound.denominator unit
    ipra_ring)

theorem harmonic_power_bound (p j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (power (sample p a b) j) (GaussianLogarithmFactorialPowerBound.numerator p j a b)
      (GaussianLogarithmFactorialPowerBound.denominator p b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (two*GaussianUpperTimeLogarithmPower.gain j a)
    (positive_product _ _ hs.andE₂ (unit_positive p)) (harmonic_power_slack p _ j a b hs hba)

theorem negative_power_bound (q j A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] bounded (power q j) A B) : Γ ⊢[PRAAx]
    bounded (power (GaussianRationalMetric.qnegative q) j) A B :=
  bound_congr (GaussianRationalParityPower.negative_power q j).eqSymm (one_mul _) (one_mul _)
    (bounded_product _ _ one one A B (le_refl one) hB (GaussianGammaRecurrenceWeightName.parity_bound j) h)

theorem reciprocal_harmonic_power_bound (p j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    bounded (power (sample p a b) j) (GaussianLogarithmFactorialPowerBound.numerator p j b a)
      (GaussianLogarithmFactorialPowerBound.denominator p a) := by
  have old := harmonic_power_bound p j b a (.andI hs.andE₂ hs.andE₁) hab
  have neg := negative_power_bound _ j _ _ (positive_product _ _ hs.andE₁ (unit_positive p)) old
  exact bound_congr (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl j)
    (GaussianEulerLowerPowerRebasing.reciprocal_sample p b a)) (.eqRefl _) (.eqRefl _) neg

theorem scaled_reference_bound (q j m a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    bounded (power (ap2 GaussianHarmonicLogarithmPower.scaledF q
      (GaussianHarmonicLogarithmPower.scaledData a b m)) j)
      (pw m j*(fact j*b*unit q+GaussianUpperTimeLogarithmPower.gain j b*a)) (a*unit q) := by
  let s := GaussianNamedNaturalScale.clock q m
  have base := reciprocal_harmonic_power_bound s j a b hs hab
  have product := bounded_product (power (naturalPoint m) j) (power (sample s a b) j)
    (pw m j) one (GaussianLogarithmFactorialPowerBound.numerator s j b a)
    (a*unit s) (le_refl one) (positive_product _ _ hs.andE₁ (unit_positive s))
    (bound_congr (.eqRefl _) (.eqRefl _) (LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily.one_pw j)
      (GaussianRationalReciprocal.bounded_power _ m one j (le_refl one) (GaussianNamedNaturalScale.natural_point_bound m))) base
  have actual := (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl j)
    (GaussianNamedNaturalScale.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF q m m (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl j) (GaussianRationalNaturalScale.natScale_as_product m _)).eqTrans
      (GaussianRationalPowerAlgebra.power_product _ _ j))
  have reduced := bound_congr actual.eqSymm (.eqRefl _) (one_mul _) product
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianNamedNaturalScale.clock_later q m)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hs.andE₁ (unit_positive s))
    (positive_product _ _ hs.andE₁ (unit_positive q)) _ reduced
  dsimp only [GaussianLogarithmFactorialPowerBound.numerator,s] at *
  ipra_le (𝔞(pw m j)*𝔞(GaussianUpperTimeLogarithmPower.gain j b)*𝔞 a*𝔞 a)*sl grow

theorem original_reference_distance (p q j m a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (rawPower p j m a b)
      (power (ap2 GaussianHarmonicLogarithmPower.scaledF q (GaussianHarmonicLogarithmPower.scaledData a b m)) j)
      (gain j m a b*(unit p+unit q)) (unit p*unit q) := by
  have oldBound := GaussianPositiveRationalLogarithm.sample_bound p (pw a m) (pw b m)
    (GaussianHarmonicLogarithmPower.power_source a b m hs)
  have refBound : Γ ⊢[PRAAx] bounded (ap2 GaussianHarmonicLogarithmPower.scaledF q
      (GaussianHarmonicLogarithmPower.scaledData a b m)) (m*(b+one)) one := by
    let s := GaussianNamedNaturalScale.clock q m
    have reciprocal := GaussianRationalReciprocal.bounded_negative _ (b+one) one (le_refl one)
      (GaussianUpperTimeLogarithmPower.harmonic_uniform_bound s b a hs.andE₁ hab)
    have low := bound_congr (GaussianEulerLowerPowerRebasing.reciprocal_sample s b a) (.eqRefl _) (.eqRefl _) reciprocal
    exact bound_congr (GaussianNamedNaturalScale.sample_at _ q m m (GaussianHarmonicLogarithmName.data a b)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianNamedNaturalScale.scaled_bound m _ (b+one) low)
  have largeOld := bounded_radius_mono _ _ _ (commonRadius m a b) one (le_refl one) (le_refl one)
    (le_of_eq_add (d := m*(b+one)) (by unfold commonRadius targetRadius; ipra_ring)) oldBound
  have largeRef := bounded_radius_mono _ _ _ (commonRadius m a b) one (le_refl one) (le_refl one)
    (le_of_eq_add (d := targetRadius m a b) (by unfold commonRadius; ipra_ring)) refBound
  exact GaussianRationalPowerDifference.power_distance_bound _ _ (commonRadius m a b) _ _ j
    (positive_product _ _ (unit_positive p) (unit_positive q)) largeOld largeRef
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (GaussianHarmonicLogarithmPower.original_logarithm_power a b m hs))

theorem original_power_slack (p q j m a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (rawPower p j m a b) (numerator p j m a b)
      (denominator p a) (auxiliaryCost j m a b) q := by
  have near := original_reference_distance p q j m a b hs hab
  have refBound := scaled_reference_bound q j m a b hs hab
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (positive_product _ _ hs.andE₁ (unit_positive q)) near refBound
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (positive_product _ _ hs.andE₁ (unit_positive q)))
    (positive_product _ _ (positive_product _ _ hs.andE₁ (unit_positive p)) (unit_positive q)) _ joined
  exact le_of_eq_add (d := zero) (by unfold numerator denominator auxiliaryCost unit; ipra_ring)

/-- The literal old log sample at the powered lower time. Its exact
factorial majorant is independent of every observation clock. -/
theorem original_power_bound (p j m a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    bounded (rawPower p j m a b) (numerator p j m a b) (denominator p a) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost j m a b)
    (positive_product _ _ hs.andE₁ (unit_positive p)) (original_power_slack p _ j m a b hs hab)

theorem original_derivative_lower_logarithm_bound (p j A a b : PTm n)
    (hs : Γ ⊢[PRAAx] source a b) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    bounded (power (GaussianPositiveRationalLogarithm.sample p (pw a (two*A)) (pw b (two*A))) j)
      (fact j*pw (two*A) j*b*unit p+gain j (two*A) a b*a) (a*unit p) :=
  original_power_bound p j (two*A) a b hs hab

theorem actual_original_lower_logarithmic_power_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 3) (var 4) ⋏ le (var 3) (var 4)) ⟶
      bounded (rawPower (var 0) (var 1) (two*var 2) (var 3) (var 4))
        (numerator (var 0) (var 1) (two*var 2) (var 3) (var 4)) (denominator (var 0) (var 3))) :=
  closeUniv 5 (.impI (original_derivative_lower_logarithm_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerLogarithmPower
