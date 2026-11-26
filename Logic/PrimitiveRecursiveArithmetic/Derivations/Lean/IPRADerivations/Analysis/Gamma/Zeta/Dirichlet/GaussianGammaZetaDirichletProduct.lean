import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate

/-!
# The Gamma product of the original cofinal Dirichlet name

This product uses the same original Gamma datum as the finite
damped-Mellin factors. The Dirichlet tail is multiplied by the
computed uniform modulus bound of that unchanged Gamma name.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletProduct

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF gammaData gammaHeight)
open GaussianGammaZetaDirichletRowDecay (block)
open GaussianGammaZetaDirichletFiniteRate (prefixData budget)
open GaussianGammaZetaMellinDampedImproper (gammaProductF gammaProductData dirichletF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "Zeta" => GaussianGammaZetaDirichletCofinal.nameF
local notation "zetaData" => GaussianGammaZetaDirichletCofinal.data

def actualGammaData (z R B A : PTm n) : PTm n := gammaData (shifted z B) (R+one) B A
def gammaBound (z R B A : PTm n) : PTm n := GaussianNameBounds.U gammaF (actualGammaData z R B A)
def rateBudget (z R B A : PTm n) : PTm n := gammaBound z R B A*budget A
def finiteData (N z R B A : PTm n) : PTm n := gammaProductData N (shifted z B) (R+one) B A
def nameF : PR 2 := multiplyF Zeta gammaF
def data (z R B A : PTm n) : PTm n := multiplyData Zeta gammaF (zetaData z R B A) (actualGammaData z R B A)

ipra_subst actualGammaData [gammaData, gammaHeight, one]
ipra_subst gammaBound
ipra_subst rateBudget
ipra_subst finiteData [one]
ipra_subst data

theorem regular (z R B A : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B A) :=
  GaussianNameArithmetic.multiply_fast Zeta gammaF _ _
    (GaussianGammaZetaDirichletCofinal.regular z R B A hz)
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular _ _ _ _
      (GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz))

theorem product_rate (N z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) :
    Γ ⊢[PRAAx] independentRate gammaProductF nameF (finiteData N z R B A) (data z R B A) (rateBudget z R B A) (unit h) := by
  let x := prefixData N z R B A
  let g := actualGammaData z R B A
  let u := zetaData z R B A
  let L := budget A
  let H := unit h
  let G := gammaBound z R B A
  let U := GaussianNameBounds.U Zeta u
  have shiftedGuard := GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz
  have hG : Γ ⊢[PRAAx] pointCN gammaF g :=
    GaussianEulerIntegralGammaIdentification.original_gamma_regular _ _ _ _ shiftedGuard
  have hZ := GaussianGammaZetaDirichletCofinal.regular z R B A hz
  have hP : Γ ⊢[PRAAx] pointCN dirichletF x :=
    GaussianGammaZetaMellinDampedImproper.dirichlet_regular N _ _ _ _ shiftedGuard
  have hGB : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound gammaF g G :=
    GaussianNameBounds.all_samples_bounded gammaF g hG
  have hUB : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound Zeta u U :=
    GaussianNameBounds.all_samples_bounded Zeta u hZ
  have dirichlet := GaussianGammaZetaDirichletCofinal.cutoff_rate N z R B A h hz hN
  have gamma := GaussianNamedDifferenceRate.self_rate gammaF g hG
  have h := GaussianNamedMultiplyRate.independent_rate dirichletF gammaF Zeta gammaF x g u g L H zero one G U
    (unit_positive h) (le_refl one) hP hG hZ hG hGB hUB dirichlet gamma
  exact GaussianNamedDifferenceRate.rate_parameters_congr gammaProductF nameF _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator rateBudget; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) h

theorem product_observations (p q N z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 gammaProductF p (finiteData N z R B A)) (ap2 nameF q (data z R B A))
      (rateNumerator (rateBudget z R B A) (unit h) p q) (rateDenominator (unit h) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (product_rate N z R B A h hz hN)

theorem actual_original_Gamma_Dirichlet_product_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (S (var 1) (var 2) (var 3) (var 4) ⟶ le (block (var 4) (var 5)) (var 0) ⟶
      independentRate gammaProductF nameF (finiteData (var 0) (var 1) (var 2) (var 3) (var 4))
        (data (var 1) (var 2) (var 3) (var 4)) (rateBudget (var 1) (var 2) (var 3) (var 4)) (unit (var 5))) :=
  closeUniv 6 (.impI (.impI (product_rate _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletProduct
