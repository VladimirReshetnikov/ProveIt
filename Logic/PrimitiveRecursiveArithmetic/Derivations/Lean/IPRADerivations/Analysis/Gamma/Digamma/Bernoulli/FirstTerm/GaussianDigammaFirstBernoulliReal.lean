import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliImproper
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReal
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Real names for the local and improper digamma remainders

The local name is already real at every observation. The improper name
has a real representative cross-equivalent to the native digamma
difference, with the same explicit dyadic convergence rate plus two.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliReal

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaFirstBernoulliEndpoints (trapezoid)
open GaussianDigammaFirstBernoulliImproper (baseF baseData original_base_rate meshDemand)
open GaussianDigammaFirstBernoulliLocal (nameF nameData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaDigammaHarmonicCells (halfReciprocal)
open GaussianNameEquivalence (cross_at crossEquivalent cross_refl)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedDampingPowerRealSamples (negative_real)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingNames (add_real constant_real log_x_real fraction_axis)
open RationalGaussianEmbedding (embed embed_axis embed_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianGammaDigammaReal.nameF
local notation "dd" => GaussianGammaDigammaReal.data
local notation "UF" => GaussianGammaDigammaElementaryBounds.nameF
local notation "ud" => GaussianGammaDigammaElementaryBounds.upperData

theorem local_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples nameF (nameData a b) :=
  add_real constantF (negativeF H) (embed (trapezoid a b)) (negativeData (hd (a+b) a))
    (constant_real _ (embed_canonical _) (embed_axis _)) (negative_real H _ (log_x_real (a+b) a))

def realF : PR 2 := GaussianNamedDifference.nameF UF D
def realData (a b : PTm n) : PTm n := GaussianNamedDifference.data (ud a b) (dd a b)

ipra_subst realData [GaussianGammaDigammaReal.data]

theorem real_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN realF (realData a b) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianGammaDigammaElementaryBounds.endpoint_regular a b _ hs) (GaussianGammaDigammaReal.name_regular a b hs)

theorem real_samples (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] realSamples realF (realData a b) := by
  let c := halfReciprocal a b
  have h := positive_product _ _ (le_succ_self one) ha
  have frac := constant_real c (ofGaussian_canonical _ _ h) (fraction_axis b (two*a) h)
  have U := add_real H (negativeF constantF) (hd a b) (negativeData c) (log_x_real a b) (negative_real _ _ frac)
  exact add_real UF (negativeF D) (ud a b) (negativeData (dd a b)) U
    (negative_real D _ (GaussianGammaDigammaReal.name_real a b))

theorem original_cross (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent baseF realF (baseData a b) (realData a b) := by
  have U := GaussianGammaDigammaElementaryBounds.endpoint_regular a b (halfReciprocal a b) hs
  exact GaussianNamedDifferenceQuotientProperness.difference_proper UF UF GaussianGammaDigammaNative.nameF D _ _ _ _
    U U (GaussianGammaDigammaNative.name_regular a b hs) (GaussianGammaDigammaReal.name_regular a b hs)
    (cross_refl _ _ U) (GaussianGammaDigammaReal.original_cross a b hs)

theorem real_base_rate (p a b Q : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hQ : Γ ⊢[PRAAx] le (meshDemand p a b) Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panelPrefix 0 2 a b (b*Q) (steps p)))
      (ap2 realF p (realData a b)) (two*a+num 38) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have cross := cross_at baseF realF (baseData a b) (realData a b) p p (original_cross a b hs)
  have e := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) cross
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (original_base_rate p a b Q hs hQ) e)

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliReal
