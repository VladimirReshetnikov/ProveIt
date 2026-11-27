import IPRADerivations.Analysis.Gamma.Zeta.Mellin.GaussianGammaZetaMellinTwoDirichlet
import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.Square.GaussianGammaZetaDirichletSquareCofinal
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentExponentialPeriod

/-!
# The Basel value of the original Mellin integral

The independent-clock identity at two reaches the original Dirichlet
name and its proved Basel value. Multiplying by the exact rational
one sixth identifies the integral with the original pi-square name
divided by six.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinBasel

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianBinetBaselName (piSquareF piSquareData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaZetaMellinTwoDirichlet (mellinData dirichletData source_at_two)
open GaussianGammaZetaDirichletSquareCofinal (sixDirichletF sixDirichletData)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one_left)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianGammaZetaMellinImproper.nameF
local notation "Z" => GaussianGammaZetaDirichletCofinal.nameF
local notation "six" => fraction (num 6) one
local notation "sixth" => fraction one (num 6)

def sixMellinF : PR 2 := multiplyF constantF I
def sixMellinData : PTm n := multiplyData constantF I six mellinData

def piOverSixF : PR 2 := multiplyF constantF piSquareF
def piOverSixData : PTm n := multiplyData constantF piSquareF sixth piSquareData

private theorem mellin_regular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN I (mellinData : PTm n) :=
  GaussianGammaZetaMellinImproper.regular oneCode one one zero (source_at_two (Γ := Γ)).andE₁

theorem scaled_mellin_Basel : Γ ⊢[PRAAx] crossEquivalent sixMellinF piSquareF
    (sixMellinData : PTm n) piSquareData := by
  have hs := constant_regular (Γ := Γ) (six : PTm n)
  have hz := GaussianGammaZetaDirichletCofinal.regular (Γ := Γ) oneCode one one one source_at_two
  have prod := multiply_cross constantF constantF I Z six six mellinData dirichletData
    hs hs mellin_regular hz (cross_refl _ _ hs)
    GaussianGammaZetaMellinTwoDirichlet.original_mellin_two_is_dirichlet
  exact cross_trans sixMellinF sixDirichletF piSquareF sixMellinData (sixDirichletData one one) piSquareData
    prod (GaussianGammaZetaDirichletSquareCofinal.original_dirichlet_Basel one one source_at_two)

private theorem sixth_times_six (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) oneF
      (multiplyData constantF constantF sixth six) x := by
  have h6 : Γ ⊢[PRAAx] le one (num 6) := by ipra_le 5
  have product : Γ ⊢[PRAAx] qmul sixth six ≐ qone :=
    (qmul_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (num 6) h6)
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point (num 6) one (le_refl one))).eqTrans
      (GaussianEulerWeightedHalfDecay.radius_reciprocal (num 6) one h6 (le_refl one))
  exact cross_trans _ _ _ _ _ _ (GaussianArctangentExponentialPeriod.constant_product sixth six)
    (cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ product)
      (GaussianArctangentExponentialPeriod.constant_one_cross x))

theorem original_mellin_Basel : Γ ⊢[PRAAx] crossEquivalent I piOverSixF
    (mellinData : PTm n) piOverSixData := by
  let x : PTm n := mellinData
  let c : PTm n := multiplyData constantF constantF sixth six
  have hi := mellin_regular (Γ := Γ)
  have hs := constant_regular (Γ := Γ) (six : PTm n)
  have hd := constant_regular (Γ := Γ) (sixth : PTm n)
  have hpi := GaussianGammaHalfPiName.name_regular (Γ := Γ) (zero : PTm n)
  have hsq := multiply_fast _ _ _ _ hpi hpi
  have collapse := multiply_cross (multiplyF constantF constantF) oneF I I c x x x
    (multiply_fast _ _ _ _ hd hs) (one_fast x) hi hi (sixth_times_six x) (cross_refl _ _ hi)
  have remove := cross_trans _ _ _ _ _ _ collapse (multiply_one_left I x hi)
  have regroup := multiply_associative constantF constantF I sixth six x hd hs hi
  have scale := multiply_cross constantF constantF sixMellinF piSquareF sixth sixth sixMellinData piSquareData
    hd hd (multiply_fast constantF I six x hs hi) hsq (cross_refl _ _ hd) scaled_mellin_Basel
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ remove)
    (cross_trans _ _ _ _ _ _ regroup scale)

theorem actual_original_Mellin_at_two_pi_squared_over_six_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] crossEquivalent I piOverSixF mellinData piOverSixData :=
  original_mellin_Basel

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinBasel
