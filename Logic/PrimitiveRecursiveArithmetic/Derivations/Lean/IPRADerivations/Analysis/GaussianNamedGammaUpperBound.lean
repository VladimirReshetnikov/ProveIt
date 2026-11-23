import IPRADerivations.Analysis.GaussianNamedHalfPlaneCorrection
import IPRADerivations.Analysis.GaussianEulerIntegralUpperBound
import IPRADerivations.Analysis.GaussianNamedEulerQuadrature

/-!
# The exact A + D_R bound for the original named Gamma and Euler integral

A convex correction of each decoded input preserves the original computed
radius and the exact real margin 1/A. Continuity compares the original
named Gamma with these corrected rational inputs. The temporary weaker
certificate 1/(2A) is used only for the continuity query; original reciprocal
certificate overlap returns to A before applying the encoded upper bound.
One finite Euclidean gap removes the auxiliary precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaUpperBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source threshold radius numerator denominator actual_late_source)
open GaussianNamedHalfPlaneCorrection (correctedNumerator correctedDenominator point original_source point_distance)
open GaussianNamedGamma (nameF data)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianGammaHalfPlaneInputContinuity (modulus reciprocal_source)
open GaussianEulerIntegralUpperTransfer (paperConstant)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (f : PR 2) (s x A : PTm n) : PTm n :=
  threshold A+succ (modulus s (radius f x) (two*A))+
    GaussianFastValueCut.exponent (two*radius f x) (modulus s (radius f x) (two*A))
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (s x A : PTm n) :
    Syn.subst σ (clock f s x A) = clock f (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ A) := by simp [clock]

private theorem weaker_source (z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source z R B (two*A) := by
  have old := zle_toZ h.andE₂.andE₂
  have weaker : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z (two*A) B := by
    apply zle_of_toZ (B+two*PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat A*ComplexLogarithmRemainder.re z))
    simp only [ZT.toZ_ofNat,ZT.toZ_mul] at old ⊢
    dsimp only [PolynomialBisection.slack]
    ipra_simps
    linear_combination 2*old
  exact .andI (positive_product _ _ (le_of_eq_add (d := one) (by ipra_ring)) h.andE₁) (.andI h.andE₂.andE₁ weaker)

private theorem late_input (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedGammaLateInput.input f s (clock f s x A) x A :=
  .andI h (.andI (le_trans (le_add_right _ _) (le_add_right _ _))
    (le_trans (le_add_left _ _) (le_add_right _ _)))

private theorem corrected_distance (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalHorner.ofGaussian (numerator f (clock f s x A) x) (denominator f (clock f s x A) x))
      (point f (clock f s x A) x) one (unit (modulus s (radius f x) (two*A))) := by
  let r := clock f s x A
  let m := modulus s (radius f x) (two*A)
  let d := GaussianFastValueCut.exponent (two*radius f x) m
  have query : Γ ⊢[PRAAx] le ((two*radius f x)*unit m) (unit d) := GaussianFastValueCut.query_budget _ _
  have growth : Γ ⊢[PRAAx] le (unit d) (unit r) := GaussianExponentialReference.unit_monotone (le_add_left _ _)
  have budget := le_trans query growth
  have original := distance_symmetric _ _ _ _ (unit_positive r) (point_distance f r x h.andE₁)
  exact distance_radius_mono _ _ _ _ one (unit m) (unit_positive r) (unit_positive m)
    (le_congr (.eqRefl _) (by ipra_ring) budget) original

private theorem corrected_source (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianGammaHalfPlaneInputContinuity.source (correctedNumerator f (clock f s x A) x)
      (radius f x) (correctedDenominator f (clock f s x A) x) A :=
  .andI (original_source f _ _ _ h) (GaussianNameBounds.U_positive f x)

private theorem norm_after_distance (z w a c D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hd : Γ ⊢[PRAAx] distanceBounded z w a D) (hw : Γ ⊢[PRAAx] bounded w c D) : Γ ⊢[PRAAx]
    bounded z (a+c) D :=
  bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hD hD hd hw)

/-- All three Gamma observations use their actual original reciprocal
programs, including the independent A and 2A certificate clocks. -/
theorem original_gamma_budget (f : PR 2) (p s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    slack (ap2 (nameF f) p (data x A)) (paperConstant A (radius f x)*unit p+one) (unit p) (num 8) s := by
  let r := clock f s x A
  let z := correctedNumerator f r x
  let B := correctedDenominator f r x
  let R := radius f x
  let C := paperConstant A R
  let U := unit s
  let P := unit p
  let D := P*U
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hP hU
  have native := original_source f r x A h
  have corrected : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A := corrected_source f s x A h
  have doubled : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B (two*A) :=
    .andI (weaker_source _ _ _ _ native) (GaussianNameBounds.U_positive f x)
  have exactBound := GaussianEulerIntegralUpperBound.original_gamma_bound s z R B A corrected
  have base : Γ ⊢[PRAAx] bounded (ap2 gammaF s (gammaData z R B A)) (C*D+P) D :=
    bounded_radius_mono _ _ _ _ _ hU hD (le_congr (by dsimp only [C,D]; ipra_ring) (.eqRefl _) (le_refl _)) exactBound
  have cert := GaussianGammaRadiusOverlap.original_Gamma_observation_overlap s s z R R B one (two*A) one A
    (reciprocal_source z R B (two*A) doubled) (reciprocal_source z R B A corrected)
  have cert' := distance_radius_mono _ _ _ _ (two*P) D (positive_product _ _ hU hU) hD
    (le_congr (by dsimp only [D,U,P]; ipra_ring) (.eqRefl _) (le_refl _)) cert
  have doubledBound := norm_after_distance _ _ _ _ D hD cert' base
  have step := GaussianGammaHalfPlaneInputContinuity.original_gamma_observations s s s
    (numerator f r x) z R (denominator f r x) B (two*A)
    (GaussianNamedGammaLateInput.encoded_source f s r x A (late_input f s x A h)) doubled (corrected_distance f s x A h)
  have step' := distance_radius_mono _ _ _ _ (num 3*P) D
    (denominator_positive _ _ _ hU) hD (le_congr (by dsimp only [rateNumerator,rateDenominator,D,U,P]; ipra_ring)
      (.eqRefl _) (le_refl _)) step
  have oldBound := norm_after_distance _ _ _ _ D hD step' doubledBound
  have late := GaussianNamedGammaLateInput.original_observations f p s s r x A (late_input f s x A h)
  have late' := distance_radius_mono _ _ _ _ (U+two*P) D (denominator_positive _ _ _ hU) hD
    (le_congr (by dsimp only [rateNumerator,rateDenominator,D,U,P]; ipra_ring) (.eqRefl _) (le_refl _)) late
  have final := norm_after_distance _ _ _ _ D hD late' oldBound
  exact bounded_radius_mono _ _ _ _ _ hD hD
    (le_congr (by dsimp only [C,D,U,P]; unfold unit; ipra_ring) (.eqRefl _) (le_refl _)) final

theorem original_gamma_bound (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF f) p (data x A)) (paperConstant A (radius f x)*unit p+one) (unit p) :=
  slack_removal_at _ _ _ (num 8) (unit_positive p) (original_gamma_budget f p _ x A h)

theorem original_improper_budget (f : PR 2) (p s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    slack (ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A))
      (paperConstant A (radius f x)*unit p+one) (unit p) two s := by
  let I := ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A)
  let G := ap2 (nameF f) s (data x A)
  let U := unit s
  let P := unit p
  let C := paperConstant A (radius f x)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hD : Γ ⊢[PRAAx] le one (P*U) := positive_product _ _ hP hU
  have cross := GaussianNamedEulerQuadrature.original_named_Euler_integral_is_Gamma f x A h
  have near : Γ ⊢[PRAAx] distanceBounded I G (P+U) (P*U) :=
    GaussianNameEquivalence.cross_at (GaussianNamedEulerQuadrature.nameF f) (nameF f) (data x A) (data x A) p s cross
  have base : Γ ⊢[PRAAx] bounded G (C*U+one) U := original_gamma_bound f s x A h
  have norm := GaussianReconstructionRoots.norm_from_distance I G (P+U) (P*U) (C*U+one) U hD hU near base
  exact bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hD hU) hD
    (le_congr (by dsimp only [C,P,U]; unfold unit; ipra_ring) (.eqRefl _) (le_refl _)) norm

theorem original_improper_bound (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A))
      (paperConstant A (radius f x)*unit p+one) (unit p) :=
  slack_removal_at _ _ _ two (unit_positive p) (original_improper_budget f p _ x A h)

theorem original_named_Gamma_A_D_R_bound_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ bounded (ap2 (nameF f) (var 0) (data (var 1) (var 2)))
      (paperConstant (var 2) (radius f (var 1))*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 3 (.impI (original_gamma_bound f _ _ _ Prf.hyp0))

theorem original_named_Euler_integral_A_D_R_bound_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ bounded (ap2 (GaussianNamedEulerQuadrature.nameF f) (var 0) (data (var 1) (var 2)))
      (paperConstant (var 2) (radius f (var 1))*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 3 (.impI (original_improper_bound f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaUpperBound
