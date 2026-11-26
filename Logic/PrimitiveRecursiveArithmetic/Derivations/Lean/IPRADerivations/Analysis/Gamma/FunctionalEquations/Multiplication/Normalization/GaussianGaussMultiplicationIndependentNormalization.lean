import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Normalization.GaussianGaussMultiplicationNormalization
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussIndependentSquareRoot

/-!
# Gauss normalization with the independent reference square-root sampler

The coefficient uses the original positive-base complex power and the
bounded search reading only the actual doubled π family power divided by
the modulus. The Gamma name appears only in the final product.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationIndependentNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianGaussMultiplicationCofinalRows (scaledData scaled_regular limit_power_regular)
open GaussianGaussMultiplicationCofinalProducts (leftF leftData rightF rightData)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianGammaGaussIndependentSquareRoot.nameF
local notation "W" => GaussianGammaGaussPositiveReference.nameF

def normalizerF : PR 2 := multiplyF powerF S
def normalizerData (z R B N x : PTm n) : PTm n :=
  multiplyData powerF S (limitData z R B (succ N)) (GaussianGammaGaussIndependentSquareRoot.nameData N x)
def normalizedF : PR 2 := multiplyF normalizerF gammaF
def normalizedData (z R B N d x : PTm n) : PTm n :=
  multiplyData normalizerF gammaF (normalizerData z R B N x) (scaledData z R B (succ N) d)

theorem normalizer_cross (z R B N a d x : PTm n) (h : Γ ⊢[PRAAx] source z R B (succ N) a d) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGaussMultiplicationNormalization.normalizerF normalizerF
      (GaussianGaussMultiplicationNormalization.normalizerData z R B N x) (normalizerData z R B N x) := by
  let P := limitData z R B (succ N)
  let v := GaussianGammaGaussPositiveReference.nameData N x
  let w := GaussianGammaGaussIndependentSquareRoot.nameData N x
  have hP := limit_power_regular z R B (succ N) a d h
  have hV := GaussianGammaGaussPositiveReference.name_regular (Γ := Γ) N x
  have e := GaussianGammaGaussIndependentSquareRoot.positive_reference_cross (Γ := Γ) N x
  have hW : Γ ⊢[PRAAx] pointCN S w := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) e
  exact multiply_cross powerF powerF W S P P v w hP hP hV hW (cross_refl _ _ hP) e

theorem normalized_right (z R B N a d x : PTm n) (h : Γ ⊢[PRAAx] source z R B (succ N) a d) :
    Γ ⊢[PRAAx] crossEquivalent rightF normalizedF (rightData z R B (succ N) d) (normalizedData z R B N d x) := by
  let F := GaussianGaussMultiplicationNormalization.normalizerF
  let A := GaussianGaussMultiplicationNormalization.normalizerData z R B N x
  let C := normalizerData z R B N x
  let Z := scaledData z R B (succ N) d
  have e := normalizer_cross z R B N a d x h
  have hF : Γ ⊢[PRAAx] pointCN F A := cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)
  have hC : Γ ⊢[PRAAx] pointCN normalizerF C := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e) e
  have hZ := scaled_regular z R B (succ N) a d h
  exact cross_trans _ _ _ _ _ _ (GaussianGaussMultiplicationNormalization.normalized_right z R B N a d x h)
    (multiply_cross F normalizerF gammaF gammaF A C Z Z hF hC hZ hZ e (cross_refl _ _ hZ))

theorem normalize_Gauss (z R B N a d x : PTm n) (h : Γ ⊢[PRAAx] source z R B (succ N) a d)
    (e : Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z R B (succ N) d) (rightData z R B (succ N) d)) :
    Γ ⊢[PRAAx] crossEquivalent leftF normalizedF (leftData z R B (succ N) d) (normalizedData z R B N d x) :=
  cross_trans _ _ _ _ _ _ e (normalized_right z R B N a d x h)

theorem actual_Gauss_independent_normalized_right_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 1) (var 2) (succ (var 3)) (var 4) (var 5) ⟶
        crossEquivalent rightF normalizedF (rightData (var 0) (var 1) (var 2) (succ (var 3)) (var 5))
          (normalizedData (var 0) (var 1) (var 2) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (normalized_right _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationIndependentNormalization
