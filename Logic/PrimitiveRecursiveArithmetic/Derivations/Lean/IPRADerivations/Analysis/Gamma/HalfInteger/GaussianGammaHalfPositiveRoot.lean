import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSquareLimit
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralPositiveLower
import IPRADerivations.Analysis.Gamma.Names.Symmetry.GaussianGammaRealValues

/-!
# Positive real-root certificate for the original Gamma value at one half

The lower estimate from the original Euler integral supplies a rational
margin, and conjugation identifies the original name with its real-axis
projection. Together with the cross-name square identity these give the
positive real-root equations for the original arctangent name of π.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfPositiveRoot

open_ipra
open GaussianGammaHalfSquareLimit (gammaHalf gammaSquareF gammaSquare gamma_source gamma_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaRealValues (axisF)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEulerIntegralPositiveLower (realSource)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction pointCN)
open RationalValueBounds (upper upper_congr upper_mono)
open ComplexLogarithmRemainder (oneCode im)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveMargin : PTm n := RationalGaussianEmbedding.embed (fraction one (num 18))

theorem half_real_source : Γ ⊢[PRAAx] realSource (oneCode : PTm n) one two two := by
  refine .andI GaussianGammaHalfIntegerDomain.half_source.andE₁ ?_
  apply ZT.derive
  simp only [GaussianRootAlgebra.im_one,ZT.toZ_ofNat,Q.mk_zero,map_zero]

theorem half_axis : Γ ⊢[PRAAx] crossEquivalent gammaF (axisF gammaF)
    (gammaHalf : PTm n) gammaHalf :=
  GaussianGammaRealValues.original_gamma_real oneCode one two one two gamma_source
    (GaussianGammaRealValues.native_real_fixed (ZT.ofNat one))

theorem lower_at (p : PTm n) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (ap2 gammaF p gammaHalf)) one (unit p) :=
  GaussianEulerIntegralPositiveLower.original_gamma_positive_lower p oneCode one two two
    half_real_source (le_refl one)

theorem lower_independent_at (p q : PTm n) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p positiveMargin)) (fstT (ap2 gammaF q gammaHalf))
      (unit p+unit q) (unit p*unit q) := by
  let x := fraction (one : PTm n) (num 18)
  let y := fstT (ap2 gammaF q gammaHalf)
  have hx : Γ ⊢[PRAAx] fstT (ap2 constantF p positiveMargin) ≐ RationalArithmetic.recode x :=
    (constant_at p positiveMargin).fstE
  have hxr : Γ ⊢[PRAAx] RationalArithmetic.recode x ≐ x :=
    RationalNormalForm.normalize_idempotent _ _ (by ipra_le 17)
  have u : Γ ⊢[PRAAx] upper x y (unit p+unit q) (unit p*unit q) :=
    upper_mono _ _ _ _ _ _ (unit_positive q)
      (lower_at q) (by ipra_le (Groth.ι (Q.mk Γ (unit q)))^2)
  exact upper_congr (hx.eqTrans hxr).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) u

private theorem shift_gammaHalf : Syn.shift (gammaHalf : PTm n) = (gammaHalf : PTm (n+1)) := by
  simp [gammaHalf,Syn.shift,GaussianGammaReciprocalInverse.gammaData,
    GaussianGammaReciprocalInverse.gammaHeight,GaussianBoundedInverseApartness.height,
    GaussianBoundedInverseApartness.productError]

private theorem shift_margin : Syn.shift (positiveMargin : PTm n) = (positiveMargin : PTm (n+1)) := by
  simp [positiveMargin,Syn.shift,fraction]

theorem half_lower : Γ ⊢[PRAAx] realOrder constantF gammaF (positiveMargin : PTm n) gammaHalf := by
  refine .allI (.allI ?_)
  change (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
    upper (fstT (ap2 constantF (var 1) (Syn.shift (Syn.shift (positiveMargin : PTm n)))))
      (fstT (ap2 gammaF (var 0) (Syn.shift (Syn.shift (gammaHalf : PTm n)))))
      (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))
  rw [shift_gammaHalf,shift_gammaHalf,shift_margin,shift_margin]
  exact lower_independent_at (var 1) (var 0)

def rootCertificate (x : PTm n) : Fm PTm n :=
  pointCN gammaF gammaHalf ⋏
    (crossEquivalent gammaF (axisF gammaF) gammaHalf gammaHalf ⋏
      (realOrder constantF gammaF positiveMargin gammaHalf ⋏
        crossEquivalent gammaSquareF GaussianGammaHalfPiName.nameF gammaSquare x))

theorem positive_root (x : PTm n) : Γ ⊢[PRAAx] rootCertificate x :=
  .andI gamma_regular (.andI half_axis (.andI half_lower
    (GaussianGammaHalfSquareLimit.original_half_square_is_pi x)))

theorem actual_Gamma_half_positive_real_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (rootCertificate (var 0)) :=
  closeUniv 1 (positive_root _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfPositiveRoot
