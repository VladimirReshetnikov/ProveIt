import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNamedRadius

/-!
# The actual encoded Gamma reference of a named real projection

Canonical equality of two independently encoded input fractions gives
cross-equivalence of the original Gamma programs. Applying this to the
literal decoded projection keeps both native denominators and the common
numerical disk. Thus named real Gamma observations can be compared with
the native real part of the very same late complex input observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedReference

open_ipra
open GaussianNamedRightHalfPlane (source radius numerator denominator threshold actual_late_source)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianGammaRealValues (axisF)
open GaussianGammaHalfPlaneInputContinuity (modulus)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem equal_fraction_observations (p q z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A)
    (hw : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source w R D A)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 gammaF p (gammaData z R B A)) (ap2 gammaF q (gammaData w R D A))
      (unit p+unit q) (unit p*unit q) := by
  let X := qsub (ap2 gammaF p (gammaData z R B A)) (ap2 gammaF q (gammaData w R D A))
  let t := GaussianRationalSlackRemoval.precision X (unit p+unit q) (unit p*unit q) one
  have close0 := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ofGaussian z B) (unit (modulus t R A)) (unit_positive _)
  have close := distance_congr (.eqRefl _) he (.eqRefl _) (.eqRefl _) close0
  have query := distance_radius_mono _ _ _ _ one (unit (modulus t R A)) (unit_positive _) (unit_positive _)
    (le_of_eq_add (d := unit (modulus t R A)) (by ipra_ring)) close
  have bound := GaussianGammaHalfPlaneInputContinuity.original_gamma_observations p q t z w R B D A hz hw query
  have hs : Γ ⊢[PRAAx] slack X (unit p+unit q) (unit p*unit q) one t :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator unit; ipra_ring)
      (by unfold rateDenominator unit; ipra_ring) bound
  exact slack_removal_at _ _ _ one (positive_product _ _ (unit_positive p) (unit_positive q)) hs

ipra_subst gammaData [GaussianGammaReciprocalInverse.gammaHeight]

theorem equal_fraction_cross (z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A)
    (hw : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source w R D A)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (gammaData z R B A) (gammaData w R D A) := by
  refine .allI (.allI ?_)
  have zs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) := by
    simpa [Fm.shift,Syn.shift,GaussianGammaHalfPlaneInputContinuity.source] using hz.shift.shift
  have ws : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source
      (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift A)) := by
    simpa [Fm.shift,Syn.shift,GaussianGammaHalfPlaneInputContinuity.source] using hw.shift.shift
  have es : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] ofGaussian (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) ≐
      ofGaussian (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using he.shift.shift
  simpa only [crossEquivalent,subst_gammaData,Syn.shift] using equal_fraction_observations (var 1) (var 0)
      (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift A)) zs ws es

def realEncodedData (f : PR 2) (r x A R : PTm n) : PTm n :=
  gammaData (argument (numerator f r x)) R (denominator f r x) (two*A)

ipra_subst realEncodedData

theorem projected_encoded_cross (f : PR 2) (r x A R : PTm n)
    (h : Γ ⊢[PRAAx] source f x A) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (realEncodedData f r x A R)
      (GaussianEulerVerticalNamedRadius.encodedData (axisF f) r x A R) := by
  have native : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source
      (argument (numerator f r x)) (radius f x) (denominator f r x) (two*A) :=
    .andI (GaussianEulerVerticalNativeProjection.lower_source _ _ _ _ (actual_late_source f x A r h hm))
    (GaussianNameBounds.U_positive f x)
  have projected : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source
      (numerator (axisF f) r x) (radius f x) (denominator (axisF f) r x) (two*A) :=
    .andI (GaussianEulerVerticalNamedProjection.projected_late_source f r x A h hm) (GaussianNameBounds.U_positive f x)
  exact equal_fraction_cross _ _ R _ _ (two*A)
    (GaussianEulerVerticalNamedRadius.source_enlarge _ _ R _ _ native hr)
    (GaussianEulerVerticalNamedRadius.source_enlarge _ _ R _ _ projected hr)
    (GaussianEulerVerticalNamedProjection.decoded_projection f r x).eqSymm

theorem projected_independent_rate (f : PR 2) (s r x A R : PTm n)
    (h : Γ ⊢[PRAAx] source f x A) (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hd : Γ ⊢[PRAAx] le (ConciseIPRA.PTm.succ (modulus s (radius (axisF f) x) (two*A))) r)
    (hr : Γ ⊢[PRAAx] le (radius f x) R) (hp : Γ ⊢[PRAAx] le (radius (axisF f) x) R) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedGamma.nameF (axisF f)) gammaF (GaussianNamedGamma.data x A)
      (realEncodedData f r x A R) one (unit s) := by
  have projected := GaussianEulerVerticalProjection.projected_source f x A h
  have late := GaussianEulerVerticalNamedRadius.original_independent_rate (axisF f) s r x A R (.andI projected (.andI hm hd)) hp
  exact GaussianNamedRateTransport.transport (GaussianNamedGamma.nameF (axisF f)) gammaF (GaussianNamedGamma.nameF (axisF f)) gammaF
    _ _ _ _ one (unit s) (unit_positive s) late (cross_refl _ _ (GaussianNamedGamma.name_regular _ _ _ projected))
    (projected_encoded_cross f r x A R h hm hr)

theorem original_decoded_real_Gamma_reference_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source f (var 1) (var 2) ⋏ le (threshold (var 2)) (var 0) ⋏ le (radius f (var 1)) (var 3)) ⟶
      crossEquivalent gammaF gammaF (realEncodedData f (var 0) (var 1) (var 2) (var 3))
        (GaussianEulerVerticalNamedRadius.encodedData (axisF f) (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (projected_encoded_cross f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedReference
