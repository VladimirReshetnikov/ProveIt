import IPRADerivations.Analysis.Euler.PowerScaling.Quadrature.GaussianEulerPowerScalingCorrectedQuadrature
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification

/-!
# Finite Gamma power substitution at the corrected image nodes

The original affine source quadrature times e/f compares to the
ordinary Euler rows at the same rational points used by the corrected
widths, with one original inverse scale observation outside the sum.
The native right-half-plane source supplies the rescaled Gamma
parameter and its certified disk without an integrand premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFiniteSubstitution

open_ipra
open GaussianEulerPowerScalingCell (scaleSample scaleBound)
open GaussianEulerPowerScalingImageQuadrature (original_quadrature_to_image)
open GaussianEulerPowerScalingCorrectedQuadrature (correctedSum original_quadrature_to_corrected)
open GaussianEulerPowerScalingCompactName (evaluatorF fixedData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPositivePowerChartImage (query)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (k z R B A e f d h L Q S E T a C N : PTm n) : Fm PTm n :=
  GaussianEulerPowerScalingParameter.source z R B A e f L Q ⋏
    (GaussianEulerPositivePowerChartMeshJacobian.input e f d h Q S E T a C N ⋏ le (two*N) (unit (query k h Q E T)))
def numerator (p k z R B e f d h L Q S E T C N : PTm n) : PTm n :=
  (N*GaussianEulerPowerScalingCell.numerator p k z (L*R) B e f d h Q S E T C N)*GaussianEulerPowerScalingCorrectedQuadrature.denominator p k h Q E T N+
    (scaleBound z B e f d h*(N*GaussianEulerPowerScalingCorrectedQuadrature.numerator p k (L*R) h Q S E T C N))*
      GaussianEulerPowerScalingCell.denominator p k h Q E T N
def denominator (p k h Q E T N : PTm n) : PTm n :=
  GaussianEulerPowerScalingCell.denominator p k h Q E T N*GaussianEulerPowerScalingCorrectedQuadrature.denominator p k h Q E T N

theorem original_source (k z R B A e f d h L Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B A e f d h L Q S E T a C N) :
    Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactName.source z R B e f d h Q S a C E T := by
  have he := hs.andE₂.andE₁.andE₁.andE₂
  have hp := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  exact .andI (.andI (.andI hp.andE₁ (.andI he.andE₁ hp.andE₂))
    (.andI he.andE₂.andE₁ (le_congr (.eqRefl _) (mul_comm T E) he.andE₂.andE₂.andE₁)))
    hs.andE₂.andE₁.andE₁.andE₁

theorem original_finite_substitution (p k z R B A e f d h L Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B A e f d h L Q S E T a C N) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction e f) (quadrature evaluatorF p N a C E (fixedData z B e f d h S)))
      (qmul (scaleSample p z B e f d h) (correctedSum p k z B e f d h Q S E T a C N))
      (numerator p k z R B e f d h L Q S E T C N) (denominator p k h Q E T N) := by
  have atScale := GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁
  have hp := atScale.andE₁.andE₂.andE₁
  have hB := hs.andE₁.andE₁.andE₁.andE₂.andE₁.andE₁
  have hm := hs.andE₂.andE₁.andE₁
  have hc := hm.andE₁.andE₂.andE₁
  have upper := original_quadrature_to_image p k z (L*R) B e f d h Q S E T a C N
    (.andI (.andI hB hp) hs.andE₂.andE₁)
  have lower := original_quadrature_to_corrected p k z (L*R) B e f d h Q S E T a C N
    (.andI hp (.andI hm hs.andE₂.andE₂))
  have hE := hm.andE₂.andE₁
  have hN := hm.andE₂.andE₂.andE₂.andE₂
  have ha := GaussianEulerPowerScalingCell.denominator_positive p k h Q E T N hE hN
  have hU := unit_positive (Γ := Γ) (query k h Q E T)
  have hb : Γ ⊢[PRAAx] le one (GaussianEulerPowerScalingCorrectedQuadrature.denominator p k h Q E T N) := positive_product _ _
    (positive_product _ _ (positive_product _ _ hE hN) hU) (positive_product _ _ hU (unit_positive p))
  have sc := GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f d h hc
  have bound := GaussianNameBounds.sample_bound _ _ p sc
  have product := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (scaleSample p z B e f d h) _ _).eqSymm (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hb bound lower)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ ha hb upper product

theorem actual_original_finite_power_substitution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
      (var 12) (var 13) (var 14) (var 15) (var 16) (var 17) ⟶
      distanceBounded
        (qmul (fraction (var 6) (var 7)) (quadrature evaluatorF (var 0) (var 17) (var 15) (var 16) (var 13)
          (fixedData (var 2) (var 4) (var 6) (var 7) (var 8) (var 9) (var 12))))
        (qmul (scaleSample (var 0) (var 2) (var 4) (var 6) (var 7) (var 8) (var 9))
          (correctedSum (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 9) (var 11) (var 12)
            (var 13) (var 14) (var 15) (var 16) (var 17)))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8) (var 9) (var 10)
          (var 11) (var 12) (var 13) (var 14) (var 16) (var 17))
        (denominator (var 0) (var 1) (var 9) (var 11) (var 13) (var 14) (var 17))) :=
  closeUniv 18 (.impI (original_finite_substitution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFiniteSubstitution
