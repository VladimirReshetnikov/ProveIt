import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionImproperName
import IPRADerivations.Analysis.GaussianEulerIntegralGammaIdentification

/-!
# Original Gamma observations from the cofinal unit-chart density

The actual finite density sampler retains the original power and decay
programs and the original eta/top cutoff family. Its proved original
Euler equivalence composes with the proved original Euler-Gamma theorem.
Both requested observations remain independent. This identifies the
cofinal exact-chart density; arbitrary rational unit meshes are separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionImproperName (nameF data)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A : PTm n) : Fm PTm n := GaussianEulerIntegralGammaIdentification.source z R B A
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    (source z R B A).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [source]

theorem original_density_is_Gamma (z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF gammaF (data z R B A) (gammaData z R B A) :=
  cross_trans _ GaussianEulerImproperName.nameF _ _ (GaussianEulerImproperName.data z R B A) _
    (GaussianEulerUnitSubstitutionImproperName.original_improper_cross z R B A
      (GaussianEulerIntegralGammaIdentification.improper_source z R B A hs))
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A hs)

theorem original_observations (p q z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (ap2 gammaF q (gammaData z R B A))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_density_is_Gamma z R B A hs)

theorem original_density_regular (z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A) :=
  GaussianEulerUnitSubstitutionImproperName.name_regular z R B A
    (GaussianEulerIntegralGammaIdentification.improper_source z R B A hs)

theorem actual_original_unit_chart_density_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF gammaF
      (data (var 0) (var 1) (var 2) (var 3)) (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_density_is_Gamma _ _ _ _ Prf.hyp0))

theorem actual_original_unit_chart_Gamma_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
        (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 5)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (original_observations _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionGamma
