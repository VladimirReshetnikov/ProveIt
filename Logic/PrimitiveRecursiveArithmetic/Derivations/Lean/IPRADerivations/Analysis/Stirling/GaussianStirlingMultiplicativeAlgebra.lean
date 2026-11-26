import IPRADerivations.Analysis.Stirling.GaussianStirlingConstant
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# The logarithmic algebra of the normalized Stirling ratio

The exact Stirling remainder plus the logarithm of its normalizing
factor equals the original positive rational log-Gamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeAlgebra

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (three add_sample_error equivalent_of_envelope)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (canonical canonical_unique qadd qadd_canonical qadd_represents positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open GaussianRationalMetric (distanceBounded qsub qsub_represents)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub)
open GaussianStirlingNames (nameF nameData name_regular source point productF productData product_regular
  logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CF" => GaussianStirlingConstant.nameF
local notation "CD" => GaussianStirlingConstant.nameData

abbrev remainderF : PR 2 := GaussianNamedDifference.nameF nameF CF
def remainderData (a b x : PTm n) : PTm n := GaussianNamedDifference.data (nameData a b) (CD x)
abbrev normalizationSumF : PR 2 := addF CF productF
def normalizationSumData (a b x : PTm n) : PTm n := addData (CD x) (productData a b)
abbrev normalizationF : PR 2 := GaussianNamedDifference.nameF normalizationSumF constantF
def normalizationData (a b x : PTm n) : PTm n := GaussianNamedDifference.data (normalizationSumData a b x) (point a b)
abbrev sumF : PR 2 := addF remainderF normalizationF
def sumData (a b x : PTm n) : PTm n := addData (remainderData a b x) (normalizationData a b x)

ipra_subst remainderData

ipra_subst normalizationSumData

ipra_subst normalizationData

ipra_subst sumData

theorem remainder_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN remainderF (remainderData a b x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (name_regular a b hs) (GaussianStirlingConstant.name_regular x)

theorem normalization_sum_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN normalizationSumF (normalizationSumData a b x) :=
  add_fast _ _ _ _ (GaussianStirlingConstant.name_regular x) (product_regular a b hs)

theorem normalization_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN normalizationF (normalizationData a b x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (normalization_sum_regular a b x hs) (constant_regular _)

private theorem cancellation_value (g t x c : PTm n) (hg : Γ ⊢[PRAAx] canonical g) : Γ ⊢[PRAAx]
    qadd (qsub (qadd (qsub g t) x) c) (qsub (qadd c t) x) ≐ g := by
  let D := rawDen g*rawDen t*rawDen x*rawDen c
  let G := scale (rawDen t*rawDen x*rawDen c) (rawGaussian g)
  let T := scale (rawDen g*rawDen x*rawDen c) (rawGaussian t)
  let X := scale (rawDen g*rawDen t*rawDen c) (rawGaussian x)
  let C := scale (rawDen g*rawDen t*rawDen x) (rawGaussian c)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _
    (positive_product _ _ (raw_den_positive g) (raw_den_positive t)) (raw_den_positive x)) (raw_den_positive c)
  have rg : Γ ⊢[PRAAx] GaussianRationalHorner.represents g G D :=
    rescale_to _ _ _ _ _ (raw_represents g) (by unfold D; ipra_ring)
  have rt : Γ ⊢[PRAAx] GaussianRationalHorner.represents t T D :=
    rescale_to _ _ _ _ _ (raw_represents t) (by unfold D; ipra_ring)
  have rx : Γ ⊢[PRAAx] GaussianRationalHorner.represents x X D :=
    rescale_to _ _ _ _ _ (raw_represents x) (by unfold D; ipra_ring)
  have rc : Γ ⊢[PRAAx] GaussianRationalHorner.represents c C D :=
    rescale_to _ _ _ _ _ (raw_represents c) (by unfold D; ipra_ring)
  have lhs := qadd_represents _ _ _ _ D hD
    (qsub_represents _ _ _ _ D hD (qadd_represents _ _ _ _ D hD (qsub_represents _ _ _ _ D hD rg rt) rx) rc)
    (qsub_represents _ _ _ _ D hD (qadd_represents _ _ _ _ D hD rc rt) rx)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) hg hD (hrv := rg)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add,re_sub,im_sub] <;> ring

set_option maxHeartbeats 700000 in
private theorem cancellation_error (p a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData a b x)) (ap2 logGammaF p (logGammaData a b))
      (num 27) (unit p) := by
  let G := logGammaData a b
  let T := productData a b
  let X := point a b
  let C := CD x
  let g := ap2 logGammaF p G
  let t := ap2 productF p T
  let v := ap2 constantF p X
  let c := ap2 CF p C
  have hp := unit_positive (Γ := Γ) p
  have hG := log_gamma_regular a b hs
  have hT := product_regular a b hs
  have hX := constant_regular (Γ := Γ) X
  have hC := GaussianStirlingConstant.name_regular (Γ := Γ) x
  have hA := name_regular a b hs
  have hD := GaussianNamedDifference.name_regular logGammaF productF G T hG hT
  have eX := distance_refl_zero v _ hp
  have eC := distance_refl_zero c _ hp
  have eD := GaussianNamedDifference.sample_error logGammaF productF G T p hG hT
  have eA := distance_triangle_same _ _ _ _ _ _ hp
    (add_sample_error GaussianStirlingNames.differenceF constantF (GaussianStirlingNames.differenceData a b) X p hD hX)
    (sum_distance _ _ _ _ _ _ _ hp eD eX)
  have eR := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error nameF CF (nameData a b) C p hA hC)
    (difference_distance _ _ _ _ _ _ _ hp eA eC)
  have eN := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error normalizationSumF constantF (normalizationSumData a b x) X p
      (normalization_sum_regular a b x hs) hX)
    (difference_distance _ _ _ _ _ _ _ hp (add_sample_error CF productF C T p hC hT) eX)
  have last := distance_triangle_same _ _ _ _ _ _ hp
    (add_sample_error remainderF normalizationF (remainderData a b x) (normalizationData a b x) p
      (remainder_regular a b x hs) (normalization_regular a b x hs))
    (sum_distance _ _ _ _ _ _ _ hp eR eN)
  have can := (GaussianSignedNameExponentialOrder.real_sample_at _ _ p
    (GaussianStirlingNames.log_gamma_real (Γ := Γ) a b)).andE₁
  exact distance_congr (.eqRefl _) (cancellation_value g t v c can) (by unfold three; ipra_ring) (.eqRefl _) last

theorem logarithmic_cancellation (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent sumF logGammaF (sumData a b x) (logGammaData a b) := by
  refine equivalent_of_envelope _ _ _ _ (num 27)
    (add_fast _ _ _ _ (remainder_regular a b x hs) (normalization_regular a b x hs))
    (log_gamma_regular a b hs) (.allI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Syn.shift,Fm.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift] using
    cancellation_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift x) h

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeAlgebra
