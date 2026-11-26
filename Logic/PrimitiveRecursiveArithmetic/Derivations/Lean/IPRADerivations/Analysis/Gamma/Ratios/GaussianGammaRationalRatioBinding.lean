import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalLogGautschi
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication

/-!
# Exact recovery of the original Gamma numerator from its ratio name

Adding back the logarithmic denominator recovers the original logarithm.
The production exponential product and Gamma recovery then certify the
ratio by multiplying it by the actual Gamma denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalRatioBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_commutative add_associative add_negative add_zero zeroF zero_at zero_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedDifference (nameF data name_regular)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular gammaData)
open GaussianStirlingLogDuplication (exponential_regular exponential_gamma)
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => logGammaF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "G" => GaussianGammaReciprocalInverse.gammaF

private theorem zero_data (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (zero_fast _)
  refine .allI ?_
  exact (zero_at _ (Syn.shift x)).eqTrans (zero_at _ (Syn.shift y)).eqSymm

theorem difference_add_recover (F H : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hh : Γ ⊢[PRAAx] pointCN H y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (nameF F H) H) F (addData (data x y) y) x := by
  let N := negativeF H
  let z := negativeData y
  have hz := negative_fast H y hh
  have a := add_associative F N H x z y hf hz hh
  have b := add_commutative N H z y hz hh
  have n := add_negative H y hh
  have inner := cross_trans _ _ _ _ _ _ b (cross_trans _ _ _ _ _ _ n (zero_data y x))
  have c := add_cross F F (addF N H) zeroF x x (addData z y) x hf hf
    (add_fast _ _ _ _ hz hh) (zero_fast _) (cross_refl _ _ hf) inner
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ c (GaussianNameRingLaws.add_zero F x hf))

theorem ratio_balance (a b r : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E ratioExponentF) G) G
      (multiplyData (E ratioExponentF) G (ed ratioExponentF (ratioExponentData a b r)) (gammaData (a+r) b))
      (gammaData (a+b) b) := by
  let F := ratioExponentF
  let d := ratioExponentData a b r
  let x := logGammaData (a+b) b
  let y := logGammaData (a+r) b
  let v := gammaData (a+r) b
  let U (f : PR 2) (x : PTm n) := GaussianNameBounds.U f x
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hZ : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := log_gamma_regular (a+b) b hZ
  have hy := log_gamma_regular (a+r) b hY
  have hd := ratio_exponent_regular a b r ha hb
  have recovery := difference_add_recover P P x y hx hy
  have eq := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent F P P (U F d) (U P y) (U P x) d y x
    (exponential_input _ _ hd) (exponential_input _ _ hy) (exponential_input _ _ hx) recovery
  have dx := exponential_regular F d hd
  have lifted := GaussianGammaAdjacentCutoff.multiply_cross (E F) (E F) G (E P) (ed F d) (ed F d) v (ed P y)
    dx dx (GaussianStirlingGammaLogarithm.gamma_regular (a+r) b hY) (exponential_regular P y hy)
    (cross_refl _ _ dx) (cross_symm _ _ _ _ (exponential_gamma (a+r) b hY))
  exact cross_trans _ _ _ _ _ _ lifted (cross_trans _ _ _ _ _ _ eq (exponential_gamma (a+b) b hZ))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalRatioBinding
