import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogRatio
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate

/-!
# Uniform numerical convergence of the Gauss multiplication powers

The common multiplier is (mz-1), with (z) the represented Gaussian
rational argument. The logarithm bound (1/N) gives an original
exponential rate with an explicit constant depending only on (m) and
the radius of (z).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationPowerRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGaussMultiplicationLogarithm (top top_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product qone_bounded)
open GaussianRationalSyntheticDivision (qone)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def multiplier (z B m : PTm n) : PTm n :=
  qsub (ofGaussian (ComplexLogarithmRemainder.scale m z) B) qone

def amplification (R m : PTm n) : PTm n := m*(R+one)
def limitLogData (m : PTm n) : PTm n := GaussianPositiveRationalLogarithm.data one m
def rowLogData (m N : PTm n) : PTm n := GaussianPositiveRationalLogarithm.data N (top m N)
def logCap (m : PTm n) : PTm n := GaussianNameBounds.U logF (limitLogData m)+num 3
def radius (R m : PTm n) : PTm n := amplification R m*logCap m
def exponentF : PR 2 := GaussianBoundedConstantProductName.nameF logF
def exponentData (z R B m x : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data (amplification R m) (multiplier z B m) x
def powerF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def powerData (z R B m x : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (radius R m) (exponentData z R B m x)
def coefficient (R m : PTm n) : PTm n :=
  GaussianRadiusExponentialLipschitzRate.factor (radius R m)*amplification R m

ipra_subst multiplier
ipra_subst amplification
ipra_subst limitLogData
ipra_subst rowLogData
ipra_subst logCap
ipra_subst radius
ipra_subst exponentData
ipra_subst powerData
ipra_subst coefficient

theorem multiplier_bound (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one := by
  let u := ComplexLogarithmRemainder.scale m z
  have scaled := ComplexLogarithmRemainder.bounded_scale m hz
  have hu : Γ ⊢[PRAAx] bounded (ofGaussian u B) (m*R) one :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB (le_refl one)
      (GaussianRationalHorner.ofGaussian_represents u B hB)
      (le_congr (by ipra_ring) (by ipra_ring) scaled)
  have neg := GaussianRationalReciprocal.bounded_negative (Γ := Γ) qone one one (le_refl one) qone_bounded
  have joint := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) hu neg
  have simple : Γ ⊢[PRAAx] bounded (multiplier z B m) (m*R+one) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul one) joint
  apply bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) _ simple
  dsimp [amplification]
  ipra_le sl hm

theorem limit_log_regular (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] pointCN logF (limitLogData m) :=
  GaussianPositiveRationalLogarithm.name_regular one m (.andI (le_refl one) hm)

theorem row_log_regular (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN logF (rowLogData m N) :=
  GaussianPositiveRationalLogarithm.name_regular N (top m N) (.andI hN (top_positive m N hm hN))

theorem limit_log_bound_at (m p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] bounded (ap2 logF p (limitLogData m)) (logCap m) one := by
  exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_of_eq_add (d := num 3) (by dsimp [logCap]; ipra_ring))
    (GaussianNameBounds.sample_bound _ _ _ (limit_log_regular m hm))

theorem row_log_bound_at (m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] bounded (ap2 logF p (rowLogData m N)) (logCap m) one := by
  let P := unit p
  have hp := unit_positive (Γ := Γ) p
  have raw := GaussianNamedInverseRate.rate_at logF logF (rowLogData m N) (limitLogData m) one N p p
    (GaussianGaussMultiplicationLogRatio.ratio_log_independent_rate m N hm hN)
  have close := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (num 3) one
    (GaussianNamedInverseRate.denominator_positive N p p hN) (le_refl one) (by
      dsimp [rateNumerator,rateDenominator]
      ipra_le (𝔞 P*𝔞 P)*sl hN+(2*𝔞 N*𝔞 P)*sl hp) raw
  have bound := GaussianReconstructionRoots.norm_from_distance _ _ (num 3) one
    (GaussianNameBounds.U logF (limitLogData m)) one (le_refl one) (le_refl one) close
    (GaussianNameBounds.sample_bound _ _ _ (limit_log_regular m hm))
  exact bound_congr (.eqRefl _) (by dsimp [logCap]; ipra_ring) (one_mul _) bound

private theorem exponent_bound_at (z R B m x p : PTm n)
    (hc : Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one)
    (hx : Γ ⊢[PRAAx] bounded (ap2 logF (GaussianBoundedConstantProductName.clock p (amplification R m)) x)
      (logCap m) one) : Γ ⊢[PRAAx] bounded (ap2 exponentF p (exponentData z R B m x)) (radius R m) one :=
  bound_congr (GaussianBoundedConstantProductName.sample_at logF p (amplification R m) (multiplier z B m) x).eqSymm
    (.eqRefl _) (one_mul _) (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hc hx)

theorem row_power_input (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius R m) (exponentData z R B m (rowLogData m N)) := by
  have hc := multiplier_bound z R B m hm hB hz
  refine .andI (GaussianBoundedConstantProductName.name_regular logF _ _ _ (.andI (row_log_regular m N hm hN) hc)) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (multiplier (sh z) (sh B) (sh m)) (amplification (sh R) (sh m)) one :=
    by simpa [Fm.shift,Syn.shift,sh] using hc.shift
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  have hNs : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hN.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,sh] using exponent_bound_at
    (sh z) (sh R) (sh B) (sh m) (rowLogData (sh m) (sh N)) (var 0) hs (row_log_bound_at _ _ _ hms hNs)

theorem limit_power_input (z R B m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius R m) (exponentData z R B m (limitLogData m)) := by
  have hc := multiplier_bound z R B m hm hB hz
  refine .andI (GaussianBoundedConstantProductName.name_regular logF _ _ _ (.andI (limit_log_regular m hm) hc)) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (multiplier (sh z) (sh B) (sh m)) (amplification (sh R) (sh m)) one :=
    by simpa [Fm.shift,Syn.shift,sh] using hc.shift
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,sh] using exponent_bound_at
    (sh z) (sh R) (sh B) (sh m) (limitLogData (sh m)) (var 0) hs (limit_log_bound_at _ _ hms)

theorem exponent_rate (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    independentRate exponentF exponentF (exponentData z R B m (rowLogData m N))
      (exponentData z R B m (limitLogData m)) (amplification R m) N :=
  GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by ipra_ring) (.eqRefl _)
    (GaussianBoundedConstantProductRate.original_rate logF logF (amplification R m) (multiplier z B m)
      (rowLogData m N) (limitLogData m) one N hN (multiplier_bound z R B m hm hB hz)
      (GaussianGaussMultiplicationLogRatio.ratio_log_independent_rate m N hm hN))

/-- An explicit (1/N) comparison for the original exponential programs,
with a uniform coefficient and an independent error at each clock. -/
theorem power_rate (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    independentRate powerF powerF (powerData z R B m (rowLogData m N))
      (powerData z R B m (limitLogData m)) (coefficient R m) N :=
  GaussianRadiusExponentialLipschitzRate.independent_rate exponentF exponentF (radius R m) _ _ (amplification R m) N
    (.andI hN (.andI (row_power_input z R B m N hm hN hB hz)
      (.andI (limit_power_input z R B m hm hB hz) (exponent_rate z R B m N hm hN hB hz))))

theorem actual_gauss_multiplication_power_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ (le one (var 4) ⋏ (le one (var 2) ⋏
      ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2)))) ⟶
      independentRate powerF powerF (powerData (var 0) (var 1) (var 2) (var 3) (rowLogData (var 3) (var 4)))
        (powerData (var 0) (var 1) (var 2) (var 3) (limitLogData (var 3))) (coefficient (var 1) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (power_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationPowerRate
