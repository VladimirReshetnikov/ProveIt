import IPRADerivations.Analysis.Euler.GaussianEulerQuadraticImproperKernel
import IPRADerivations.Analysis.Euler.GaussianEulerSquareFactorInverse
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification

/-!
# The original quadratic Euler improper kernel recovers actual Gamma

The actual cofinal unfactored kernel is multiplied by its original
factor 2*(c/d)^(z/B). The proved original Euler identification and the
actual factor inverse cancel within the original normalized name
arithmetic. The final target is the unchanged original Gamma program,
with independent requested observations and no new analytic premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSquareIntegrand (factorF factorData)
open GaussianEulerSquareFactorInverse (inverseFactorF inverseFactorData)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Kernel" => GaussianEulerQuadraticImproperKernel.nameF
local notation "kdata" => GaussianEulerQuadraticImproperKernel.data
local notation "Euler" => GaussianEulerImproperName.nameF

abbrev source (z R B A c d : PTm n) : Fm PTm n := GaussianEulerQuadraticImproperKernel.source z R B A c d
abbrev productF : PR 2 := multiplyF inverseFactorF gammaF
def productData (z R B A c d : PTm n) : PTm n := multiplyData inverseFactorF gammaF (inverseFactorData z B c d) (gammaData z R B A)
abbrev forwardF : PR 2 := multiplyF factorF Kernel
def forwardData (z R B A c d : PTm n) : PTm n := multiplyData factorF Kernel (factorData z B c d) (kdata z R B A c d)

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    Syn.subst σ (productData z R B A c d) = productData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [productData]
@[simp] theorem subst_forwardData {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    Syn.subst σ (forwardData z R B A c d) = forwardData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [forwardData,GaussianEulerSquareIntegrand.factorData,GaussianEulerPositiveScalingConstant.scaleData]

theorem constant_source (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingConstant.source B c d :=
  .andI hs.andE₁.andE₁.andE₂.andE₁.andE₁ hs.andE₂

theorem product_regular (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx] pointCN productF (productData z R B A c d) :=
  multiply_fast inverseFactorF gammaF _ _ (GaussianEulerSquareFactorInverse.inverse_regular z B c d (constant_source z R B A c d hs))
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A hs.andE₁)

theorem forward_regular (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx] pointCN forwardF (forwardData z R B A c d) :=
  multiply_fast factorF Kernel _ _ (GaussianEulerSquareFactorInverse.factor_regular z B c d (constant_source z R B A c d hs))
    (GaussianEulerQuadraticImproperKernel.name_regular z R B A c d hs)

/-- The actual unfactored improper kernel is the actual inverse factor
multiplied by the unchanged original Gamma name. -/
theorem original_kernel_is_inverse_factor_Gamma (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent Kernel productF (kdata z R B A c d) (productData z R B A c d) := by
  have hi := GaussianEulerSquareFactorInverse.inverse_regular z B c d (constant_source z R B A c d hs)
  have he := GaussianEulerImproperName.name_regular z R B A (GaussianEulerIntegralGammaIdentification.improper_source z R B A hs.andE₁)
  have hg := GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A hs.andE₁
  have replace := GaussianGammaAdjacentCutoff.multiply_cross inverseFactorF inverseFactorF Euler gammaF
    (inverseFactorData z B c d) (inverseFactorData z B c d) (GaussianEulerImproperName.data z R B A) (gammaData z R B A)
    hi hi he hg (cross_refl _ _ hi) (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A hs.andE₁)
  exact cross_trans _ _ _ _ _ _ (GaussianEulerQuadraticImproperKernel.original_Euler_cross z R B A c d hs) replace

/-- Multiplication by the same actual original factor recovers the
original Gamma program, before any external value interpretation. -/
theorem original_forward_Gamma (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent forwardF gammaF (forwardData z R B A c d) (gammaData z R B A) := by
  let x := factorData z B c d
  let y := inverseFactorData z B c d
  let u := kdata z R B A c d
  let v := gammaData z R B A
  have hc := constant_source z R B A c d hs
  have hx := GaussianEulerSquareFactorInverse.factor_regular z B c d hc
  have hy := GaussianEulerSquareFactorInverse.inverse_regular z B c d hc
  have hu := GaussianEulerQuadraticImproperKernel.name_regular z R B A c d hs
  have hv := GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A hs.andE₁
  have first := GaussianGammaAdjacentCutoff.multiply_cross factorF factorF Kernel productF
    x x u (productData z R B A c d) hx hx hu (product_regular z R B A c d hs)
    (cross_refl _ _ hx) (original_kernel_is_inverse_factor_Gamma z R B A c d hs)
  have regroup := GaussianNameRingLaws.multiply_associative factorF inverseFactorF gammaF x y v hx hy hv
  have inverse := cross_trans _ _ _ _ _ _ (GaussianEulerSquareFactorInverse.factor_inverse_product z B c d hc)
    (GaussianBoundedInverseApartness.ones_equivalent (GaussianEulerPositiveScalingConstant.exponentData z B c d) v)
  have reduce := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF factorF inverseFactorF) GaussianNameRingLaws.oneF gammaF gammaF
    (multiplyData factorF inverseFactorF x y) v v v (multiply_fast factorF inverseFactorF x y hx hy)
    (GaussianNameRingLaws.one_fast v) hv hv inverse (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ regroup)
    (cross_trans _ _ _ _ _ _ reduce (GaussianNameRingLaws.multiply_one_left gammaF v hv)))

theorem original_observations (p q z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 forwardF p (forwardData z R B A c d)) (ap2 gammaF q (gammaData z R B A))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_forward_Gamma z R B A c d hs)

theorem original_kernel_observations (p q z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 Kernel p (kdata z R B A c d)) (ap2 productF q (productData z R B A c d))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_kernel_is_inverse_factor_Gamma z R B A c d hs)

theorem actual_original_quadratic_kernel_is_inverse_factor_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent Kernel productF (kdata (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_kernel_is_inverse_factor_Gamma _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_quadratic_forward_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent forwardF gammaF (forwardData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (original_forward_Gamma _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_quadratic_forward_Gamma_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (ap2 forwardF (var 0) (forwardData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 5))) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticGamma
