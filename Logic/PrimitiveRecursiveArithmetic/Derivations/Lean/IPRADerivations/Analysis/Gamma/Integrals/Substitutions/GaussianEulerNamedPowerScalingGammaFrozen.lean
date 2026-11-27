import IPRADerivations.Analysis.Euler.PowerScaling.Named.Parameters.GaussianEulerNamedPowerScalingParameterFrozen
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaRadiusOverlap

/-!
# Named Gamma of the rescaled parameter at frozen exponents

The exact exponent decoded at each sufficiently late input index can be
used in the original rational rescaling. The result compares the actual
named Gamma and the original rational Gamma at independent output times.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingGammaFrozen

open_ipra
open GaussianEulerNamedPowerScalingParameter (nameF data source named_half_plane)
open GaussianEulerNamedPowerScalingParameterFrozen (frozenPoint original_frozen_source original_frozen_rate)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianGammaHalfPlaneInputContinuity (modulus reciprocal_source)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaInverseConjugation renaming subst_original_gamma_data → subst_gammaData

variable {n : ℕ} {Γ : List (Fm PTm n)}

def frozenData (f : PR 2) (k z R B A x E T : PTm n) : PTm n :=
  gammaData (scaled z (denominator f k x)) (E*R) (B*numerator f k x) (T*A)

def commonRadius (f : PR 2) (z R B x E : PTm n) : PTm n :=
  radius (nameF f) (data z R B x E)+E*R

def frozenClock (f : PR 2) (s z R B A x E T : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (two*(R*(E*E)))
    (modulus (succ s) (commonRadius f z R B x E) (two*(T*A)))

ipra_subst frozenClock [commonRadius]

ipra_subst frozenData [scaled, numerator, denominator]

private theorem enlarge (z R S B A C : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A)
    (hr : Γ ⊢[PRAAx] le R S)
    (hc : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z C B)
    (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    GaussianGammaHalfPlaneInputContinuity.source z S B C := by
  have scaled := mul_le_mul_right B hr
  have disk := le_trans h.andE₁.andE₂.andE₁.andE₂
    (le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right (R*B) scaled))
      (mul_le_mul_right (S*B) scaled))
  exact .andI (.andI hC (.andI (.andI h.andE₁.andE₂.andE₁.andE₁ disk) hc)) (le_trans h.andE₂ hr)

private theorem double_margin (z A B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z A B) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.realLower z (two*A) B := by
  let u := ZT.ofNat B
  let v := ZT.ofNat A*ComplexLogarithmRemainder.re z
  have e := zle_toZ h
  unfold GaussianEulerLowerPowerCoefficients.realLower
  apply zle_of_toZ (two*PolynomialBisection.slack u v+B)
  dsimp only [u,v,PolynomialBisection.slack]
  unfold GaussianEulerLowerPowerCoefficients.realLower at h
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination 2*e

private theorem input_budget (j k m D : PTm n)
    (hj : Γ ⊢[PRAAx] le (succ (succ m)) j)
    (hk : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (two*D) m) k) : Γ ⊢[PRAAx]
    le (rateNumerator D (unit k) j j*unit m) (one*rateDenominator (unit k) j j) := by
  have e : Γ ⊢[PRAAx] unit (succ m) ≐ unit m*two := pw_succ two m
  have e' : Γ ⊢[PRAAx] unit (succ (succ m)) ≐ unit m*two*two :=
    (pw_succ two (succ m)).eqTrans (congrMul e (.eqRefl two))
  have U := le_congr e' (.eqRefl _) (unit_monotone hj)
  have K := le_trans (GaussianFastValueCut.query_budget (two*D) m) (unit_monotone hk)
  have first := mul_le_mul_right (unit j*unit j) K
  have second := mul_le_mul_right (unit k*unit j) U
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring)
      (add_le_add₂ first second))

private theorem input_close (f : PR 2) (j k m z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T)
    (hj : Γ ⊢[PRAAx] le (succ (succ m)) j)
    (hk : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (two*(R*(E*E))) m) k) : Γ ⊢[PRAAx]
    distanceBounded (GaussianNamedGamma.point (nameF f) (data z R B x E) j)
      (frozenPoint f k z B x) one (unit m) := by
  let P := nameF f
  let y := data z R B x E
  let w := frozenPoint f k z B x
  have sourceW := original_frozen_source f k z R B A x E T hs
  have wc := ofGaussian_canonical (scaled z (denominator f k x)) (B*numerator f k x)
    sourceW.andE₁.andE₂.andE₁.andE₁
  have den := denominator_positive (unit k) j j (unit_positive (Γ := Γ) k)
  have obs := rate_at P constantF y w (R*(E*E)) (unit k) j j (original_frozen_rate f k z R B A x E T hs)
  have raw := distance_congr (.eqRefl _) (constant_at j w) (.eqRefl _) (.eqRefl _) obs
  have recoded := GaussianFastValueCut.recode_distance_bound _ _ _ _ den raw
  have close := distance_congr (.eqRefl (GaussianNamedGamma.point P y j))
    (GaussianExponentialReference.recode_fixed w wc) (.eqRefl _) (.eqRefl _) recoded
  exact distance_radius_mono _ _ _ _ _ _ den (unit_positive m) (input_budget j k m (R*(E*E)) hj hk) close

private theorem common_independent_rate (s z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A)
    (hw : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source w R D A)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (modulus s R A))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF (gammaData z R B A) (gammaData w R D A) one (unit s) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have zl : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianGammaHalfPlaneInputContinuity.source (sh z) (sh R) (sh B) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianGammaHalfPlaneInputContinuity.source,
      GaussianEulerLowerPowerCoefficients.source, GaussianEulerUpperPowerCoefficients.source] using hz.shift.shift
  have wl : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianGammaHalfPlaneInputContinuity.source (sh w) (sh R) (sh D) (sh A) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianGammaHalfPlaneInputContinuity.source,
      GaussianEulerLowerPowerCoefficients.source, GaussianEulerUpperPowerCoefficients.source] using hw.shift.shift
  have dl : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (ofGaussian (sh z) (sh B)) (ofGaussian (sh w) (sh D)) one
        (unit (modulus (sh s) (sh R) (sh A))) := by simpa [Fm.shift,Syn.shift,sh] using hd.shift.shift
  simpa only [independentRate,sh,Syn.shift,subst_gammaData,GaussianCoefficientNameBounds.subst_unit,
    PTm.subst_succ,PTm.subst_zero] using
    GaussianGammaHalfPlaneInputContinuity.original_gamma_observations (var 1) (var 0) (sh s)
      (sh z) (sh w) (sh R) (sh B) (sh D) (sh A) zl wl dl

private theorem reduce_rate (F G : PR 2) (y w s : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F G y w (one+one) (unit (succ s))) :
    Γ ⊢[PRAAx] independentRate F G y w one (unit s) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (sh y) (sh w) (one+one) (unit (succ (sh s))) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  have obs := rate_at F G (sh y) (sh w) (one+one) (unit (succ (sh s))) (var 1) (var 0) hs
  have step : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] unit (succ (sh s)) ≐ two*unit (sh s) :=
    (pw_succ two (sh s)).eqTrans (mul_comm _ _)
  have eqn := congrAdd (.eqRefl ((one+one)*unit (var 1)*unit (var 0)))
    (congrMul step (.eqRefl (unit (var 1)+unit (var 0))))
  have eqd := congrMul (congrMul step (.eqRefl (unit (var 1)))) (.eqRefl (unit (var 0)))
  have changed := distance_congr (.eqRefl _) (.eqRefl _) eqn eqd obs
  have db : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (two*unit (sh s)) :=
    positive_product _ _ RationalAlgebra.two_positive (unit_positive (sh s))
  have out := distance_radius_mono _ _ _ _ (rateNumerator one (unit (sh s)) (var 1) (var 0))
    (rateDenominator (unit (sh s)) (var 1) (var 0)) (denominator_positive _ _ _ db)
    (denominator_positive _ _ _ (unit_positive (sh s)))
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) changed
  simpa only [independentRate,sh,Syn.shift,GaussianCoefficientNameBounds.subst_unit,PTm.subst_succ,PTm.subst_zero] using out

/-- The frozen index is arbitrary above a bound independent of both Gamma observation times. -/
theorem original_independent_rate (f : PR 2) (s k z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T)
    (hk : Γ ⊢[PRAAx] le (frozenClock f s z R B A x E T) k) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedGamma.nameF (nameF f)) gammaF
      (GaussianNamedGamma.data (data z R B x E) (T*A)) (frozenData f k z R B A x E T) one (unit s) := by
  let P := nameF f
  let y := data z R B x E
  let C := T*A
  let S := commonRadius f z R B x E
  let t := succ s
  let m := modulus t S (two*C)
  let d := succ (modulus t (radius P y) (two*C))
  let j := threshold C+d+succ (succ m)
  let z₁ := GaussianNamedRightHalfPlane.numerator P j y
  let B₁ := GaussianNamedRightHalfPlane.denominator P j y
  let z₂ := scaled z (denominator f k x)
  let B₂ := B*numerator f k x
  have named := named_half_plane f z R B A x E T hs
  have hj : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input P t j y C :=
    .andI named (.andI (le_trans (le_add_right _ _) (le_add_right _ _))
      (le_trans (le_add_left _ _) (le_add_right _ _)))
  have first := GaussianNamedGammaLateInput.original_independent_rate P t j y C hj
  have l₀ := GaussianNamedGammaLateInput.encoded_source P t j y C hj
  have r₀ := original_frozen_source f k z R B A x E T hs
  have hl := enlarge z₁ (radius P y) S B₁ (two*C) (two*C) l₀ (le_add_right _ _)
    l₀.andE₁.andE₂.andE₂ l₀.andE₁.andE₁
  have hr := enlarge z₂ (E*R) S B₂ C (two*C) r₀ (le_add_left _ _)
    (double_margin z₂ C B₂ r₀.andE₁.andE₂.andE₂) l₀.andE₁.andE₁
  have close := input_close f j k m z R B A x E T hs (le_add_left _ _) hk
  have mixed := common_independent_rate t z₁ z₂ S B₁ B₂ (two*C) hl hr close
  have left := GaussianGammaRadiusOverlap.original_Gamma_overlap z₁ (radius P y) S B₁ one (two*C) one (two*C)
    (reciprocal_source _ _ _ _ l₀) (reciprocal_source _ _ _ _ hl)
  have right := GaussianGammaRadiusOverlap.original_Gamma_overlap z₂ (E*R) S B₂ one C one (two*C)
    (reciprocal_source _ _ _ _ r₀) (reciprocal_source _ _ _ _ hr)
  have second := GaussianNamedRateTransport.transport gammaF gammaF gammaF gammaF _ _
    (GaussianNamedGammaLateInput.encodedData P j y C) (frozenData f k z R B A x E T)
    one (unit t) (unit_positive _) mixed left right
  exact reduce_rate _ _ _ _ s (GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ one (unit t) one
    (unit_positive t) first second)

theorem actual_named_rescaled_Gamma_frozen_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source f (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      le (frozenClock f (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 1)) ⟶
      independentRate (GaussianNamedGamma.nameF (nameF f)) gammaF
        (GaussianNamedGamma.data (data (var 2) (var 3) (var 4) (var 6) (var 7)) (var 8*var 5))
        (frozenData f (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) one (unit (var 0))) :=
  closeUniv 9 (.impI (original_independent_rate f _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingGammaFrozen
