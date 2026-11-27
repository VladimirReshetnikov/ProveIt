import IPRADerivations.Analysis.Euler.ExponentialSubstitution.Kernels.GaussianEulerExponentialSubstitutionIntegrand
import IPRADerivations.Analysis.Logarithm.PositiveAxis.Increments.GaussianPositiveRationalLogarithmIncrement
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# A cell of the logarithmic image of the original Euler grid

The image cell uses the difference of the original logarithm observations
as its width and the original exponential of z/B times the logarithm
minus time as its left value. The first-order width change and the
pointwise Jacobian identity give the actual finite Euler cell comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogCell

open_ipra
open GaussianEulerExponentialSubstitutionIntegrand (exponentialF data)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRationalLogarithmIncrement (increment)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z B a b T : PTm n) : Fm PTm n :=
  GaussianEulerIntegrandName.source z B a b ⋏ le a (T*b)
def imageCell (p z B a b c : PTm n) : PTm n :=
  qmul (increment p p a b c) (ap2 exponentialF p (data z B a b))
def errorNumerator (p a c T M : PTm n) : PTm n :=
  M*(c*c*unit p+two*(a*a))+c*(one+T)*a
def errorDenominator (p a : PTm n) : PTm n := (a*a)*unit p

ipra_subst source
ipra_subst imageCell [increment]

theorem linear_cell (a b c w : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qmul (fraction c a) (qmul (fraction a b) w) ≐ qmul (fraction c b) w := by
  have equal : Γ ⊢[PRAAx] qmul (fraction c a) (fraction a b) ≐ fraction c b :=
    (GaussianEulerDampedTimeRate.fraction_product c a a b ha hb).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_comm _ _) (.eqRefl _)).eqTrans
        (GaussianCompactRiemannSplit.fraction_cancel a c b ha hb))
  exact (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr equal (.eqRefl _))

theorem original_cell_error (p z B a b c T M : PTm n) (h : Γ ⊢[PRAAx] source z B a b T)
    (hg : Γ ⊢[PRAAx] bounded (ap2 exponentialF p (data z B a b)) M one) : Γ ⊢[PRAAx]
    distanceBounded (imageCell p z B a b c) (qmul (fraction c b) (GaussianEulerIntegrandName.sample p z B a b))
      (errorNumerator p a c T M) (errorDenominator p a) := by
  let P := unit p
  let G := ap2 exponentialF p (data z B a b)
  let W := increment p p a b c
  let J := fraction c a
  let V := qmul (fraction a b) (GaussianEulerIntegrandName.sample p z B a b)
  let D := errorDenominator p a
  have ha := h.andE₁.andE₂.andE₁
  have hb := h.andE₁.andE₂.andE₂
  have hp := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ ha ha) hp
  have hOriginal : Γ ⊢[PRAAx] le one (GaussianPositiveRationalLogarithmIncrement.errorDenominator p p a) :=
    positive_product _ _ (positive_product _ _ ha ha) (positive_product _ _ hp hp)
  have widthError : Γ ⊢[PRAAx] distanceBounded W J (c*c*P+two*(a*a)) D :=
    distance_radius_mono _ _ _ _ _ _ hOriginal hD
      (le_of_eq_add (d := zero) (by
        unfold GaussianPositiveRationalLogarithmIncrement.errorNumerator GaussianPositiveRationalLogarithmIncrement.errorDenominator
        dsimp only [D,errorDenominator,P]
        ipra_ring))
      (GaussianPositiveRationalLogarithmIncrement.original_increment p p a b c ha hb)
  have first := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (.eqRefl _) (.eqRefl _) (GaussianNamedDifferenceQuotient.scale_distance G W J M _ _ hD hg widthError)
  have valueError : Γ ⊢[PRAAx] distanceBounded G V (one+T) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
      (le_of_eq_add (d := zero) (by dsimp only [P]; ipra_ring))
      (GaussianEulerExponentialSubstitutionIntegrand.original_raw_observations p p z B a b T h.andE₁ h.andE₂)
  have hJ : Γ ⊢[PRAAx] bounded J c a :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ ha).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded c a ha)
  have rightRaw : Γ ⊢[PRAAx] distanceBounded (qmul J G) (qmul J V) (c*(one+T)) (a*P) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference J G V).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product J (qsub G V) c a (one+T) P ha hp hJ valueError)
  have right := distance_radius_mono _ _ _ _ (c*(one+T)*a) D (positive_product _ _ ha hp) hD
    (le_of_eq_add (d := zero) (by dsimp only [D,errorDenominator]; ipra_ring)) rightRaw
  exact distance_congr (.eqRefl _) (linear_cell a b c _ ha hb) (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first right)

theorem actual_original_logarithmic_image_cell_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 6) ⋏
      bounded (ap2 exponentialF (var 0) (data (var 1) (var 2) (var 3) (var 4))) (var 7) one) ⟶
      distanceBounded (imageCell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (qmul (fraction (var 5) (var 4)) (GaussianEulerIntegrandName.sample (var 0) (var 1) (var 2) (var 3) (var 4)))
        (errorNumerator (var 0) (var 3) (var 5) (var 6) (var 7)) (errorDenominator (var 0) (var 3))) :=
  closeUniv 8 (.impI (original_cell_error _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogCell
