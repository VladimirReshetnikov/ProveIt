import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.DenominatorBounds.GaussianBinetBoseLinearApproximation
import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.Endpoint.GaussianBinetBoseIntegrandBound
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Time variation of the original Bose reciprocal on positive panels

The time horizon gives one radius for the original scaled Pi
observations. A positive lower time margin gives one inverse
bound for the original normalized reciprocals.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseReciprocalTimeRate

open_ipra
open GaussianBinetBoseExponential (scaleF scaleData expF expData expRadius exp_input exp_regular piClock)
open GaussianBinetBoseLinearApproximation (coefficient coefficient_bound coefficient_distance scale_factor)
open GaussianBinetBoseDenominator (nameF data reciprocalF reciprocalData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def radius (T : PTm n) : PTm n := num 10*T
def denominatorGain (T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (radius T)*num 10
def gain (E T : PTm n) : PTm n := E*E*denominatorGain T

ipra_subst radius
ipra_subst gain [denominatorGain]

private theorem scale_bound (p a b T : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] bounded (ap2 scaleF p (scaleData false a b)) (radius T) one := by
  have bnd := GaussianEulerExponentCompactBounds.fraction_bound a b T hb ht
  exact bound_congr (scale_factor p a b hb).eqSymm (by unfold radius; ipra_ring) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) bnd (coefficient_bound (piClock p a)))

private theorem common_input (a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input scaleF (radius T) (scaleData false a b) := by
  refine .andI (exp_input false a b hb).andE₁ (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hB : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift
  have hT : Δ ⊢[PRAAx] le (s a) (s T*s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,s,subst_radius,GaussianBinetBoseExponential.subst_scaleData]
    using scale_bound (var 0) (s a) (s b) (s T) hB hT

private theorem scale_diagonal (p a b c d T H Q : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hc : Γ ⊢[PRAAx] le c (T*d)) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 scaleF p (scaleData false a b)) (ap2 scaleF p (scaleData false c d))
      (diagonalNumerator (num 10*H) Q (num 4*T) p) (diagonalDenominator Q p) := by
  let s := piClock p a
  let t := piClock p c
  let U := unit s
  let V := unit t
  let P := unit p
  let N := Q*P
  have hp := unit_positive (Γ := Γ) p
  have hn := positive_product _ _ hQ hp
  have growS : Γ ⊢[PRAAx] le P U := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have growT : Γ ⊢[PRAAx] le P V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have old := coefficient_distance (Γ := Γ) s t
  have close : Γ ⊢[PRAAx] distanceBounded (coefficient s) (coefficient t) (num 4) P := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) hp ?_ old
    ipra_le 2*𝔞(U)*sl growT+2*𝔞(V)*sl growS
  let left := fraction a b
  let right := fraction c d
  have first := GaussianApproximateInverseDistance.multiply_distance (coefficient s) left right (num 10) H Q hQ
    (coefficient_bound s) h
  have second := GaussianApproximateInverseDistance.multiply_distance right (coefficient s) (coefficient t) T (num 4) P hp
    (GaussianEulerExponentCompactBounds.fraction_bound c d T hd hc) close
  have co := distance_congr (qmul_commutative (coefficient s) left) (qmul_commutative (coefficient s) right)
    (.eqRefl _) (.eqRefl _) first
  have oneStep := distance_radius_mono _ _ _ _ ((num 10*H)*P) N hQ hn
    (le_of_eq_add (d := zero) (by dsimp only [N]; ipra_ring)) co
  have next := distance_radius_mono _ _ _ _ ((num 4*T)*Q) N hp hn
    (le_of_eq_add (d := zero) (by dsimp only [N]; ipra_ring)) second
  exact distance_congr (scale_factor p a b hb).eqSymm (scale_factor p c d hd).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hn oneStep next)

private theorem scale_rate (a b c d T H Q : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hc : Γ ⊢[PRAAx] le c (T*d)) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) H Q) :
    Γ ⊢[PRAAx] independentRate scaleF scaleF (scaleData false a b) (scaleData false c d) (num 10*H) Q := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 4*T) hQ
    (exp_input false a b hb).andE₁ (exp_input false c d hd).andE₁
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have b' : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift
  have d' : Δ ⊢[PRAAx] le one (s d) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hd.shift
  have c' : Δ ⊢[PRAAx] le (s c) (s T*s d) := by simpa [Δ,s,Fm.shift,Syn.shift] using hc.shift
  have Q' : Δ ⊢[PRAAx] le one (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hQ.shift
  have ds : Δ ⊢[PRAAx] distanceBounded (fraction (s a) (s b)) (fraction (s c) (s d)) (s H) (s Q) := by
    simpa [Δ,s,Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,s,GaussianBinetBoseExponential.subst_scaleData,PTm.subst_mul,PTm.subst_num] using
    scale_diagonal (var 0) (s a) (s b) (s c) (s d) (s T) (s H) (s Q) b' d' c' Q' ds

theorem denominator_rate (a b c d T H Q : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] le a (T*b)) (hc : Γ ⊢[PRAAx] le c (T*d))
    (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) H Q) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data a b) (data c d) (denominatorGain T*H) Q := by
  let x := scaleData false a b
  let y := scaleData false c d
  have ax := common_input a b T hb ha
  have cy := common_input c d T hd hc
  have rx := exp_input false a b hb
  have ry := exp_input false c d hd
  have dx := GaussianExponentialRadiusIndependence.independent_radii_proper scaleF scaleF
    (expRadius a) (radius T) x x rx ax (GaussianNameEquivalence.cross_refl _ _ rx.andE₁)
  have dy := GaussianExponentialRadiusIndependence.independent_radii_proper scaleF scaleF
    (expRadius c) (radius T) y y ry cy (GaussianNameEquivalence.cross_refl _ _ ry.andE₁)
  have er := GaussianRadiusExponentialLipschitzRate.independent_rate scaleF scaleF (radius T) x y
    (num 10*H) Q (.andI hQ (.andI ax (.andI cy (scale_rate a b c d T H Q hb hd hc hQ h))))
  have orig := GaussianNamedRateTransport.transport expF expF expF expF _ _ _ _ _ Q hQ er dx dy
  have r := GaussianNamedDifferenceRate.same_right_rate expF expF GaussianNameRingLaws.oneF
    (expData false a b) (expData false c d) zero _ Q hQ (exp_regular false a b hb) (exp_regular false c d hd)
    (GaussianNameRingLaws.one_fast zero) orig
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold denominatorGain; ipra_ring) (.eqRefl _) r

theorem inverse_bound_at (p a b E : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (lower : Γ ⊢[PRAAx] le b (E*a)) : Γ ⊢[PRAAx] bounded (ap2 reciprocalF p (reciprocalData a b)) E one := by
  have hp : Γ ⊢[PRAAx] le one (num 4*a) := positive_product _ _ (by ipra_le 3) ha
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hp (le_refl one) ?_
    (GaussianBinetBoseIntegrandBound.reciprocal_bound p a b ha hb)
  ipra_le sl lower+3*𝔞(E*a)

theorem inverse_samples_bound (a b E : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (lower : Γ ⊢[PRAAx] le b (E*a)) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound reciprocalF (reciprocalData a b) E := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have a' : Δ ⊢[PRAAx] le one (s a) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using ha.shift
  have b' : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift
  have lo : Δ ⊢[PRAAx] le (s b) (s E*s a) := by simpa [Δ,s,Fm.shift,Syn.shift] using lower.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,s,GaussianBinetBoseDenominator.subst_reciprocalData] using
    inverse_bound_at (var 0) (s a) (s b) (s E) a' b' lo

theorem inverse_rate (a b c d E T H Q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (lo : Γ ⊢[PRAAx] le b (E*a)) (lo' : Γ ⊢[PRAAx] le d (E*c))
    (hi : Γ ⊢[PRAAx] le a (T*b)) (hi' : Γ ⊢[PRAAx] le c (T*d))
    (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) H Q) :
    Γ ⊢[PRAAx] independentRate reciprocalF reciprocalF (reciprocalData a b) (reciprocalData c d) (gain E T*H) Q := by
  have fa := GaussianBinetBoseDenominator.regular a b hb
  have fc := GaussianBinetBoseDenominator.regular c d hd
  have ga := GaussianBinetBoseDenominator.reciprocal_regular a b ha hb
  have gc := GaussianBinetBoseDenominator.reciprocal_regular c d hc hd
  have ra := GaussianNameReciprocal.product_one nameF b (data a b) fa (GaussianBinetBoseDenominator.apart a b ha hb)
  have rc := GaussianNameReciprocal.product_one nameF d (data c d) fc (GaussianBinetBoseDenominator.apart c d hc hd)
  have ia : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples reciprocalF (reciprocalData a b) E one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianNamedMultiplyRate.sampleBound,
      Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using inverse_samples_bound a b E ha hb lo
  have ic : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples reciprocalF (reciprocalData c d) E one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianNamedMultiplyRate.sampleBound,
      Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using inverse_samples_bound c d E hc hd lo'
  have time := denominator_rate a b c d T H Q hb hd hi hi' hQ h
  have reference := GaussianNamedInverseRate.inverse_rate nameF nameF reciprocalF reciprocalF
    (data a b) (data c d) (reciprocalData a b) (reciprocalData c d) E one (denominatorGain T*H) Q
    (.andI (le_refl one) (.andI hQ (.andI (.andI fa fc) (.andI (.andI ga gc)
      (.andI (.andI ia ic) (.andI (.andI ra rc) time))))))
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold gain; ipra_ring) (by ipra_ring) reference

end LeanProofs.IPRA.Analysis.GaussianBinetBoseReciprocalTimeRate
