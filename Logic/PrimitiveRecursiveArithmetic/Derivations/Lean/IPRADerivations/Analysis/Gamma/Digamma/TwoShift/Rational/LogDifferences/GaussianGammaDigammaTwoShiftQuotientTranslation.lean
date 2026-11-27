import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.LogDifferences.GaussianGammaDigammaTwoShiftLogGammaTranslation
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftBinding
import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Common rational translation of the original normalized Gamma ratio

The chart repair translates the base and both shifted arguments by the
same rational step. This preserves the exact encoded signed difference
in the power and transports the original normalized quotient logarithm
with an explicit linear cost.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftQuotientTranslation

open_ipra
open GaussianCompactLogarithmBounds (original_log_rate)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftBinding
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerRationalContinuity (response)
open GaussianNameArithmetic (multiplyData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianRationalHorner (canonical_unique ofGaussian_represents represents represents_congr positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRootAlgebra (sub equal_of_values re_scale im_scale re_one im_one re_sub im_sub)
open GaussianStirlingGammaLogarithm (arg logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "HD" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianGammaDigammaTwoShiftLogGammaTranslation.domain

def domain (a b c d u K C : PTm n) : Fm PTm n := D a b u K C ⋏ (D c b u K C ⋏ D d b u K C)

def gain (K C : PTm n) : PTm n := response K C+(response K C+(C+C)*K)

theorem coefficient_translation (b c d u : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] coefficient b (c+u) (d+u) ≐ coefficient b c d := by
  let a := fraction (c+u) b
  let e := fraction (d+u) b
  let x := fraction c b
  let y := fraction d b
  let z := sub (arg c) (arg d)
  have old := qsub_represents x y (arg c) (arg d) b hb (ofGaussian_represents _ _ hb) (ofGaussian_represents _ _ hb)
  have new := qsub_represents a e (arg (c+u)) (arg (d+u)) b hb (ofGaussian_represents _ _ hb) (ofGaussian_represents _ _ hb)
  have diff : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (sub (arg (c+u)) (arg (d+u))) z := by
    apply equal_of_values
    · simp only [z,arg,re_sub,re_scale,re_one]
      ipra_simps
      ring
    · simp only [z,arg,im_sub,im_scale,im_one]
      ring
  exact canonical_unique _ _ z b (qsub_canonical a e) (qsub_canonical x y) hb
    (represents_congr (.eqRefl _) diff (.eqRefl _) new) old

private theorem axis_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (fraction a b) (native a zero zero) b :=
  represents_congr (.eqRefl _)
    (GaussianRootAlgebra.equal_symm (GaussianLogGammaEulerPositiveAxis.native_axis_equal a zero (.orI₁ (.eqRefl _))))
    (.eqRefl _) (ofGaussian_represents _ _ hb)

private theorem base_distance (a b u : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (fraction (a+u) b) (fraction a b) u b := by
  have norm := GaussianGammaDigammaTwoShiftLogGammaTranslation.axis_displacement (Γ := Γ) a u
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ b u b hb hb
    (axis_represents (a+u) b hb) (axis_represents a b hb)).iffMpr
  unfold ComplexLogarithmRemainder.bounded at norm
  ipra_le 𝔞(b*b)*sl norm

theorem base_log_rate (a b u K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) (hK : Γ ⊢[PRAAx] le b (K*a)) :
    Γ ⊢[PRAAx] independentRate H H (HD (a+u) b) (HD a b) (K*u) b := by
  have hh : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (a+u) b :=
    .andI (le_trans h.andE₁ (le_add_right a u)) h.andE₂
  have hw : Γ ⊢[PRAAx] le b (K*(a+u)) := by ipra_le sl hK+𝔞 K*𝔞 u
  have old := original_log_rate (a+u) b a b K u b hh h h.andE₂ hw hK (base_distance a b u h.andE₂)
  exact GaussianNamedRateTransport.transport logF logF H H
    (GaussianPositiveRationalLogarithm.data (a+u) b) (GaussianPositiveRationalLogarithm.data a b) (HD (a+u) b) (HD a b)
    (K*u) b h.andE₂ old
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original (a+u) b hh))
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b h))

private theorem coefficient_bound (b c d C : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le c (C*b)) (hd : Γ ⊢[PRAAx] le d (C*b)) :
    Γ ⊢[PRAAx] bounded (coefficient b c d) (C+C) one := by
  have h₁ := GaussianEulerExponentCompactBounds.fraction_bound c b C hb hc
  have h₂ := GaussianEulerExponentCompactBounds.fraction_bound d b C hb hd
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one) h₁
    (GaussianRationalReciprocal.bounded_negative _ _ one (le_refl one) h₂)

private theorem equal_coefficient_rate (v w b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] v ≐ w) :
    Γ ⊢[PRAAx] independentRate constantF constantF v w zero b := by
  have hw := constant_regular (Γ := Γ) w
  have raw := GaussianNamedRateRadius.weaken constantF constantF w w zero one zero b
    (le_refl one) hb (by ipra_le 0) (GaussianNamedDifferenceRate.self_rate constantF w hw)
  exact GaussianNamedRateTransport.transport constantF constantF constantF constantF w w v w zero b hb raw
    (GaussianSignedNameExponentialOrder.constant_equal_cross v w h) (cross_refl _ _ hw)

theorem quotient_log_rate (a b c d u K C : PTm n) (hs : Γ ⊢[PRAAx] domain a b c d u K C) :
    Γ ⊢[PRAAx] independentRate quotientLogF quotientLogF (quotientLogData (a+u) b (c+u) (d+u)) (quotientLogData a b c d)
      (gain K C*u) b := by
  let v := coefficient b (c+u) (d+u)
  let w := coefficient b c d
  let p := powerLogData (a+u) b (c+u) (d+u)
  let q := powerLogData a b c d
  let x := denominatorLogData (a+u) b (c+u) (d+u)
  let y := denominatorLogData a b c d
  let G := response K C*u
  let P := (C+C)*(K*u)
  let A := GaussianNameBounds.U H (HD (a+u) b)
  have sa := hs.andE₁.andE₁
  have sc := hs.andE₂.andE₁.andE₁
  have sd := hs.andE₂.andE₂.andE₁
  have hb := sa.andE₂
  have hB := positive_product _ _ hb hb
  have sa' : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (a+u) b := .andI (le_trans sa.andE₁ (le_add_right a u)) hb
  have sc' : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (c+u) b := .andI (le_trans sc.andE₁ (le_add_right c u)) hb
  have sd' : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (d+u) b := .andI (le_trans sd.andE₁ (le_add_right d u)) hb
  have hc := hs.andE₂.andE₁.andE₂.andE₂.andE₂.andE₁
  have hd := hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hw := coefficient_bound b c d C hb (by ipra_le sl hc+𝔞 c+𝔞 u) (by ipra_le sl hd+𝔞 d+𝔞 u)
  have hV := coefficient_translation b c d u hb
  have hlog := base_log_rate a b u K sa hs.andE₁.andE₂.andE₂.andE₁
  have hr1 := GaussianHarmonicLogarithmName.name_regular (a+u) b sa'
  have hr2 := GaussianHarmonicLogarithmName.name_regular a b sa
  have raw := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator constantF H constantF H
    v (HD (a+u) b) w (HD a b) zero (K*u) b A (C+C) hb
    (constant_regular v) hr1 (constant_regular w) hr2 (GaussianNameBounds.all_samples_bounded _ _ hr1)
    (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound w (C+C) hw)
    (equal_coefficient_rate v w b hb hV) hlog
  have prod : Γ ⊢[PRAAx] independentRate powerLogF powerLogF p q P b :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ P b (by dsimp only [P]; ipra_ring) (.eqRefl _) raw
  have lower := GaussianGammaDigammaTwoShiftLogGammaTranslation.original_rate d b u K C hs.andE₂.andE₂
  have denomRaw := GaussianNamedAddRate.independent_rate logGammaF powerLogF logGammaF powerLogF
    (logGammaData (d+u) b) p (logGammaData d b) q G b P b hb hb lower prod
  have denom : Γ ⊢[PRAAx] independentRate denominatorLogF denominatorLogF x y (G+P) b :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ (G+P) b hB hb
      (le_of_eq_add (d := zero) (by simp only [GaussianNamedRateComposition.leadingNumerator]; ipra_ring)) denomRaw
  have upper := GaussianGammaDigammaTwoShiftLogGammaTranslation.original_rate c b u K C hs.andE₂.andE₁
  have rawQ := GaussianNamedDifferenceRate.original_rate logGammaF denominatorLogF logGammaF denominatorLogF
    (logGammaData (c+u) b) x (logGammaData c b) y G b (G+P) b
    (.andI (.andI hb hb) (.andI (.andI (log_gamma_regular (c+u) b sc') (denominator_log_regular (a+u) b (c+u) (d+u) sa' sd'))
      (.andI (.andI (log_gamma_regular c b sc) (denominator_log_regular a b c d sa sd)) (.andI upper denom))))
  exact GaussianNamedRateRadius.weaken quotientLogF quotientLogF _ _ _ _ (gain K C*u) b hB hb
    (le_of_eq_add (d := zero) (by simp only [GaussianNamedDifferenceRate.leadingNumerator]; dsimp only [gain,G,P]; ipra_ring)) rawQ

theorem actual_original_two_shift_quotient_chart_translation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (domain (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        independentRate quotientLogF quotientLogF
          (quotientLogData (var 0+var 4) (var 1) (var 2+var 4) (var 3+var 4))
          (quotientLogData (var 0) (var 1) (var 2) (var 3))
          (gain (var 5) (var 6)*var 4) (var 1)) :=
  closeUniv 7 (.impI (quotient_log_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftQuotientTranslation
