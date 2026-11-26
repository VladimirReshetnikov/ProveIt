import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalIntegrandSquare
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalRealSamples
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalRealRadius
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNormTransfer
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianPositiveRadiusFiniteSum

/-!
# Source-only vertical domination of each original Euler row

At the same actual query and time encoding, the unchanged complex Euler
row is bounded by the unchanged real-argument row plus four ordinary
observation tolerances. The comparator is proved nonnegative even when
the uncorrected finite real observation has a negative lower error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalPointwise

open_ipra
open GaussianEulerVerticalExponentReference (source)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerIntegrandName (nameF data sample)
open GaussianRationalL1 (rawGaussian rawDen raw_represents)
open GaussianRationalHorner (qadd positive_product)
open GaussianDominantPairAlgebra (radiusPoint radius_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRadiusFiniteSum (boundBy)
open ComplexLogarithmRemainder (re)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def corrected (q U : PTm n) : PTm n := qadd q (radiusPoint (num 4) U)
def numerator (q U : PTm n) : PTm n := GaussianEulerVerticalRealRadius.gap q U+num 3*rawDen q

theorem corrected_represents (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper RationalGaussianEmbedding.scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (corrected q U)) (ZT.ofNat (numerator q U)) (GaussianEulerVerticalRealRadius.denominator q U) := by
  have four : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (radiusPoint (num 4) U)) (ZT.ofNat (num 4)) U :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianDominantPairAlgebra.radiusNumerator,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
      (radius_represents (num 4) U hU).andE₁
  have actual := RationalRepresentations.represents_add _ _ _ _ _ _ (raw_represents q).andE₁ four
  apply GaussianRationalHorner.scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm _ (.eqRefl _) actual
  apply ZT.derive
  have e := natEq (GaussianEulerVerticalRealRadius.gap_identity (Γ := Γ) q U h)
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,numerator]
  dsimp only [ZT.toZ]
  ipra_simps
  linear_combination e

theorem corrected_positive (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hq : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis q)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper RationalGaussianEmbedding.scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (corrected q U) := by
  have radial := GaussianPositiveRealArithmetic.positive_from_representation (radiusPoint (num 4) U) (num 4) U
    (GaussianRationalHorner.ofGaussian_canonical _ _ hU) hU (radius_represents (num 4) U hU)
  exact .andI (RationalGaussianEmbedding.axis_add _ _ hq radial.andE₁)
    (GaussianRationalL1.nonnegative_of_representation _ _ _
      (GaussianEulerVerticalRealRadius.denominator_positive q U hU) (corrected_represents q U hU h))

theorem original_named_bound (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    boundBy (ap2 nameF p (data z B a b)) (corrected (ap2 nameF p (data (argument z) B a b)) (unit p)) := by
  let q := ap2 nameF p (data (argument z) B a b)
  let U := unit p
  let S := GaussianEulerVerticalRealRadius.numerator q U
  let T := GaussianEulerVerticalRealRadius.denominator q U
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hT : Γ ⊢[PRAAx] le one T := GaussianEulerVerticalRealRadius.denominator_positive q U hU
  have samples := GaussianEulerVerticalRealSamples.original_real_integrand_samples z B a b h.andE₁.andE₁ h.andE₂
  have real := GaussianSignedNameExponentialOrder.real_sample_at nameF (data (argument z) B a b) p samples
  have fixed := GaussianEulerVerticalRealSamples.real_input_fixed nameF p (data (argument z) B a b) samples
  have lower := GaussianEulerVerticalRealSamples.original_real_integrand_nonnegative p z B a b h.andE₁.andE₁ h.andE₂
  have bound := GaussianEulerVerticalRealRadius.corrected_bounds_original q U hU fixed lower
  have transferred := GaussianEulerVerticalNormTransfer.original_norm_transfer nameF nameF (data z B a b) (data (argument z) B a b) p S T hT
    (GaussianEulerIntegrandName.name_regular z B a b (.andI h.andE₁.andE₁ h.andE₂))
    (GaussianEulerIntegrandName.name_regular (argument z) B a b (.andI h.andE₁.andE₁ h.andE₂))
    (GaussianEulerVerticalIntegrandSquare.original_integrand_square z R B a b h) bound
  have finalBound : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (ap2 nameF p (data z B a b)) (numerator q U) T :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hT hU) hT
      (le_of_eq_add (d := zero) (by dsimp only [S,T,numerator,GaussianEulerVerticalRealRadius.numerator,GaussianEulerVerticalRealRadius.denominator]; ipra_ring)) transferred
  exact GaussianPositiveRadiusFiniteSum.from_representation _ _ _ _ hT (corrected_positive q U hU real.andE₂ lower)
    (corrected_represents q U hU lower) finalBound

theorem original_row_bound (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    boundBy (sample p z B a b) (qadd (sample p (argument z) B a b) (radiusPoint (num 4) (unit p))) :=
  GaussianPositiveRadiusFiniteSum.bound_congr (GaussianEulerIntegrandName.sample_at p z B a b).eqSymm
    (GaussianRationalSyntheticDivision.qadd_congr (GaussianEulerIntegrandName.sample_at p (argument z) B a b).eqSymm (.eqRefl _))
    (original_named_bound p z R B a b h)

theorem original_vertical_Euler_pointwise_domination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      boundBy (sample (var 0) (var 1) (var 3) (var 4) (var 5))
        (qadd (sample (var 0) (argument (var 1)) (var 3) (var 4) (var 5)) (radiusPoint (num 4) (unit (var 0))))) :=
  closeUniv 6 (.impI (original_row_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalPointwise
