import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactPowerVariation
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# The actual positive rational power chart (d/h)*t^(e/f)

The original Euler power parameter is the native real point e+f over f.
Its actual coefficient is proved exactly e/f. A supplied upper exponent
bound Q and scale bound S give a uniform compact disk and constant clock.
Every chart observation is the literal original power observation at that
clock, multiplied by d/h. No derivative or output-value law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChart

open_ipra
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub re_scale im_scale re_one im_one)
open GaussianEulerIntegrandName (powerF powerData coefficient)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product canonical_unique represents_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCompactLogarithmBounds (domain)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def argument (e f : PTm n) : PTm n := scale (e+f) oneCode
def parameters (e f d h Q S : PTm n) : Fm PTm n :=
  (le one e ⋏ le one f) ⋏ ((le one d ⋏ le one h) ⋏ ((le one Q ⋏ le one S) ⋏ (le e (Q*f) ⋏ le d (S*h))))
def source (e f d h Q S E T a b : PTm n) : Fm PTm n :=
  parameters e f d h Q S ⋏ (le one E ⋏ domain a b E T)
def data (e f d h S a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data S (fraction d h) (powerData (argument e f) f a b)
abbrev nameF : PR 2 := GaussianBoundedConstantProductName.nameF powerF
def clock (p S : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p S
def majorant (Q S E T : PTm n) : PTm n := S*GaussianEulerCompactPowerMajorant.majorant (Q+one) E T
def lipschitz (Q S E T : PTm n) : PTm n := S*GaussianEulerCompactPowerVariation.lipschitz (Q+one) E T

def input (e f d h Q S E T a b c v X D : PTm n) : Fm PTm n :=
  source e f d h Q S E T a b ⋏ (domain c v E T ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction c v) X D))

ipra_subst argument
ipra_subst parameters
ipra_subst source
ipra_subst data
ipra_subst clock
ipra_subst majorant [GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius, GaussianCompactLogarithmBounds.radius]
ipra_subst lipschitz
ipra_subst input

/-- Exact cancellation of the native +f and the original -1 coefficient. -/
theorem coefficient_exact (e f : PTm n) (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx]
    coefficient (argument e f) f ≐ fraction e f := by
  have native : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub (argument e f) (scale f oneCode)) (scale e oneCode) := by
    apply equal_of_values <;> simp only [argument,re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ (scale e oneCode) f (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hf) hf
    (represents_congr (.eqRefl _) native (.eqRefl _) (GaussianEulerIntegrandName.coefficient_represents (argument e f) f hf))
    (GaussianRationalHorner.ofGaussian_represents _ _ hf)

theorem argument_disk (e f Q : PTm n) (hb : Γ ⊢[PRAAx] le e (Q*f)) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (argument e f) ((Q+one)*f) := by
  have sum : Γ ⊢[PRAAx] le (e+f) ((Q+one)*f) := le_congr (.eqRefl _) (by ipra_ring) (add_le_add_right f hb)
  have same : Γ ⊢[PRAAx] normSq (argument e f) ≐ (e+f)*(e+f) :=
    (ComplexLogarithmRemainder.normSq_scale (e+f) oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact le_congr same.eqSymm (.eqRefl _) (sq_le_sq sum)

theorem scale_bound (e f d h Q S : PTm n) (hs : Γ ⊢[PRAAx] parameters e f d h Q S) : Γ ⊢[PRAAx]
    bounded (fraction d h) S one := by
  have hh := hs.andE₂.andE₁.andE₂
  have initial := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point d h hh).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded d h hh)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hh (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) hs.andE₂.andE₂.andE₂.andE₂) initial

theorem power_source (e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianEulerExponentCompactBounds.source (argument e f) (Q+one) f E :=
  .andI hs.andE₁.andE₁.andE₂ (.andI hs.andE₂.andE₁ (argument_disk e f Q hs.andE₁.andE₂.andE₂.andE₂.andE₁))

theorem name_regular (e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    pointCN nameF (data e f d h S a b) :=
  GaussianBoundedConstantProductName.name_regular powerF S (fraction d h) (powerData (argument e f) f a b)
    (.andI (GaussianEulerIntegrandName.power_regular _ _ _ _ (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₂.andE₁))
      (scale_bound e f d h Q S hs.andE₁))

theorem sample_at (p e f d h S a b : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data e f d h S a b) ≐ qmul (fraction d h) (ap2 powerF (clock p S) (powerData (argument e f) f a b)) :=
  GaussianBoundedConstantProductName.sample_at powerF p S (fraction d h) _

theorem original_bound (p e f d h Q S E T a b : PTm n) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data e f d h S a b)) (majorant Q S E T) one := by
  have old := GaussianEulerCompactPowerMajorant.original_power_observation (clock p S) (argument e f) (Q+one) f E T a b
    (power_source e f d h Q S E T a b hs) hs.andE₂.andE₂
  exact bound_congr (sample_at p e f d h S a b).eqSymm (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ S one _ one (le_refl _) (le_refl _)
      (scale_bound e f d h Q S hs.andE₁) old)

theorem original_rate (e f d h Q S E T a b c v X D : PTm n) (hs : Γ ⊢[PRAAx] input e f d h Q S E T a b c v X D) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data e f d h S a b) (data e f d h S c v) (lipschitz Q S E T*X) D := by
  have old := GaussianEulerCompactPowerVariation.original_power_rate (argument e f) (Q+one) f E T a b c v X D
    (.andI (power_source e f d h Q S E T a b hs.andE₁) (.andI hs.andE₁.andE₂.andE₂ hs.andE₂))
  have moved := GaussianBoundedConstantProductRate.original_rate powerF powerF S (fraction d h) _ _ _ D hs.andE₂.andE₂.andE₁
    (scale_bound e f d h Q S hs.andE₁.andE₁) old
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold lipschitz; ipra_ring) moved

theorem original_observations (p q e f d h Q S E T a b c v X D : PTm n) (hs : Γ ⊢[PRAAx] input e f d h Q S E T a b c v X D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data e f d h S a b)) (ap2 nameF q (data e f d h S c v))
      (rateNumerator (lipschitz Q S E T*X) D p q) (rateDenominator D p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate e f d h Q S E T a b c v X D hs)

theorem actual_original_positive_power_chart_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9))) :=
  closeUniv 10 (.impI (name_regular _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_positive_power_chart_exact_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ coefficient (argument (var 0) (var 1)) (var 1) ≐ fraction (var 0) (var 1)) :=
  closeUniv 2 (.impI (coefficient_exact _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChart
