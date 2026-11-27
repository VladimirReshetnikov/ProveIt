import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Limits.GaussianGaussMultiplicationCofinalProducts
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussPositiveReference

/-!
# The positive-normalized right-hand side of Gauss multiplication

With (m=N+1), the original cleared right-hand side has multiplier
(m^{1-mz}sqrt{(2pi)^N/m}). The root is the checked positive real
name, and the complex power uses the original positive-base logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationNormalization

open_ipra
open GaussianGaussMultiplicationCofinalProducts (leftF leftData rightF rightData innerF innerData)
open GaussianGaussMultiplicationCofinalRows (scaledData scaled_regular limit_power_regular)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (limitData)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaGaussPositiveReference (rootCertificate positive_root)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl cross_symm)
open GaussianGammaAdjacentCutoff (multiply_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianGammaGaussPositiveReference.nameF
local notation "O" => GaussianGammaGaussReferenceProduct.nameF

def normalizerF : PR 2 := multiplyF powerF S
def normalizerData (z R B N x : PTm n) : PTm n :=
  multiplyData powerF S (limitData z R B (succ N)) (GaussianGammaGaussPositiveReference.nameData N x)
def normalizedF : PR 2 := multiplyF normalizerF gammaF
def normalizedData (z R B N d x : PTm n) : PTm n :=
  multiplyData normalizerF gammaF (normalizerData z R B N x) (scaledData z R B (succ N) d)

theorem normalized_right (z R B N a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ N) a d) :
    Γ ⊢[PRAAx] crossEquivalent rightF normalizedF (rightData z R B (succ N) d) (normalizedData z R B N d x) := by
  let m := succ N
  let X := limitData z R B m
  let Y := scaledData z R B m d
  let A := GaussianGammaGaussReferenceProduct.data m
  let C := GaussianGammaGaussPositiveReference.nameData N x
  let I := innerData z R B m d
  let H := multiplyF gammaF S
  let J := multiplyF S gammaF
  let U := multiplyData gammaF S Y C
  let V := multiplyData S gammaF C Y
  have hp := limit_power_regular z R B m a d hs
  have hg := scaled_regular z R B m a d hs
  have ho := GaussianGammaGaussReferenceProduct.name_regular (Γ := Γ) m
  have hs' := GaussianGammaGaussPositiveReference.name_regular (Γ := Γ) N x
  have hi : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN innerF I := multiply_fast _ _ _ _ hp hg
  have replace := multiply_cross innerF innerF O S I I A C hi hi ho hs' (cross_refl _ _ hi)
    (GaussianGammaGaussPositiveReference.original_cross N x)
  have associate := multiply_associative powerF gammaF S X Y C hp hg hs'
  have exchange := multiply_cross powerF powerF H J X X U V hp hp
    (multiply_fast _ _ _ _ hg hs') (multiply_fast _ _ _ _ hs' hg) (cross_refl _ _ hp)
    (multiply_commutative gammaF S Y C hg hs')
  have regroup := cross_symm _ _ _ _ (multiply_associative powerF S gammaF X C Y hp hs' hg)
  exact cross_trans _ _ _ _ _ _ replace
    (cross_trans _ _ _ _ _ _ associate (cross_trans _ _ _ _ _ _ exchange regroup))

theorem normalize_Gauss (z R B N a d x : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ N) a d)
    (hM4 : Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z R B (succ N) d) (rightData z R B (succ N) d)) :
    Γ ⊢[PRAAx] crossEquivalent leftF normalizedF (leftData z R B (succ N) d) (normalizedData z R B N d x) :=
  cross_trans _ _ _ _ _ _ hM4 (normalized_right z R B N a d x hs)

theorem actual_Gauss_normalized_right_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 1) (var 2) (succ (var 3)) (var 4) (var 5) ⟶
        crossEquivalent rightF normalizedF (rightData (var 0) (var 1) (var 2) (succ (var 3)) (var 5))
          (normalizedData (var 0) (var 1) (var 2) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (normalized_right _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationNormalization
