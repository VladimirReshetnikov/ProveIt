import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerQuadraticCutoffGeometry
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteIntervalRate
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerQuadraticImproperSchedule
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate

/-!
# Actual quadratic cutoff quadrature and the original Euler improper name

The positive-width image compact integral is an actual difference of
two incomplete tails. The lower endpoint and the aligned integer upper
endpoint supply their own rates, which combine before transport through
the checked compact change of variables.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticCutoffComparison

open_ipra
open GaussianEulerQuadraticCutoffGeometry (source width lowerDenominator imageWidth imageData leftData)
open GaussianEulerQuadraticLowerEndpoint (minimumIndex)
open GaussianEulerQuadraticUpperEndpoint (preimage imageIndex)
open GaussianGammaIntegralCutoffs (etaDen height)
open GaussianEulerSquareTimeGeometry (upperEndpoint)
open GaussianEulerIncompleteName (upperF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def jacobianData (j z R B A c d : PTm n) : PTm n :=
  GaussianEulerSquareJacobianCompactName.data z R B c d one (width j A R d) (etaDen j A R) (preimage j A R d)
def gain (k j A R : PTm n) : PTm n := leadingNumerator A (unit (height k A R)) one (unit (j+num 6))
def denominator (k j A R : PTm n) : PTm n := leadingDenominator (unit (height k A R)) (unit (j+num 6))

ipra_subst jacobianData [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem original_image_rate (k j z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hj : Γ ⊢[PRAAx] le (minimumIndex k c d) j) : Γ ⊢[PRAAx]
    independentRate GaussianEulerCompactAdditivity.nameF GaussianEulerImproperName.nameF
      (imageData j z R B A c d) (GaussianEulerImproperName.data z R B A) (gain k j A R) (denominator k j A R) := by
  let W := imageWidth j A R c d
  let E := lowerDenominator j A R d
  let T := upperEndpoint c (preimage j A R d)
  let v := imageIndex j A R c d
  let L := unit (height k A R)
  let H := unit (j+num 6)
  have hc := hs.andE₂.andE₁
  have hd := hs.andE₂.andE₂
  have hw0 := GaussianEulerQuadraticCutoffGeometry.width_positive j A R d hd
  have hw : Γ ⊢[PRAAx] le one W :=
    positive_product _ _ (positive_product _ _ hc hw0) (le_trans hw0 (le_add_left _ _))
  have hE := GaussianEulerQuadraticCutoffGeometry.denominator_positive j A R d hd
  have right := (GaussianEulerQuadraticCutoffGeometry.exact_image_endpoint j A R c d hd).eqTrans
    (congrMul (GaussianEulerQuadraticUpperEndpoint.exact_image_top j A R c d hc hd).eqSymm (.eqRefl E))
  have interval : Γ ⊢[PRAAx] GaussianEulerIncompleteIntervalRate.source v z R B A c W E T :=
    .andI (.andI hs.andE₁ (.andI hc (.andI hw (.andI hE
      (GaussianEulerQuadraticCutoffGeometry.original_image_source j z R B A c d hs).andE₂.andE₂)))) right
  have cut := GaussianEulerIncompleteIntervalRate.original_later_interval_rate j v z R B A c W E T interval
    (GaussianEulerQuadraticUpperEndpoint.image_index_later j A R c d hc hd)
  have lower := GaussianEulerQuadraticLowerEndpoint.original_upper_to_Euler_rate k j z R B A c d hs hj
  have raw := GaussianNamedRateComposition.compose GaussianEulerCompactAdditivity.nameF upperF GaussianEulerImproperName.nameF
    (imageData j z R B A c d) (leftData j z R B A c d) (GaussianEulerImproperName.data z R B A)
    one H A L (unit_positive _) (unit_positive _) cut lower
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold gain leadingNumerator; ipra_ring) (by unfold denominator leadingDenominator; ipra_ring) raw

theorem original_jacobian_cutoff_rate (k j z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hj : Γ ⊢[PRAAx] le (minimumIndex k c d) j) : Γ ⊢[PRAAx]
    independentRate GaussianEulerSquareJacobianCompactName.nameF GaussianEulerImproperName.nameF
      (jacobianData j z R B A c d) (GaussianEulerImproperName.data z R B A) (gain k j A R) (denominator k j A R) := by
  have same := GaussianEulerSquareCompactComparison.original_compact_cross z R B one (width j A R d)
    (etaDen j A R) (preimage j A R d) c d (GaussianEulerQuadraticCutoffGeometry.original_square_source j z R B A c d hs)
  have moved := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _
    (GaussianEulerQuadraticCutoffGeometry.actual_image_data j z R B A c d) (.eqRefl _) same
  have he := GaussianEulerImproperName.name_regular z R B A
    (GaussianEulerIntegralGammaIdentification.improper_source z R B A hs.andE₁)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (original_image_rate k j z R B A c d hs hj)
    (cross_symm _ _ _ _ moved) (cross_refl _ _ he)

theorem actual_quadratic_Jacobian_cutoff_to_Euler_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      le (minimumIndex (var 0) (var 6) (var 7)) (var 1) ⟶
      independentRate GaussianEulerSquareJacobianCompactName.nameF GaussianEulerImproperName.nameF
        (jacobianData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (GaussianEulerImproperName.data (var 2) (var 3) (var 4) (var 5))
        (gain (var 0) (var 1) (var 5) (var 3)) (denominator (var 0) (var 1) (var 5) (var 3))) :=
  closeUniv 8 (.impI (.impI (original_jacobian_cutoff_rate _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticCutoffComparison
