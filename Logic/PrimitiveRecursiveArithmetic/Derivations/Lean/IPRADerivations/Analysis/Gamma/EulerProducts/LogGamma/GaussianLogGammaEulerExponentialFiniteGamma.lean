import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerExponentialHead
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerReciprocalInverse

/-!
# The positive exponential of an actual finite log-Gamma head

On the domain of the original pole-safe finite Gamma name, named
exponential inversion transfers the checked reciprocal-head identity to
the actual finite Gamma approximant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFiniteGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (qF qData exponentialInputData exponential_input)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData eulerHeight original_euler_inverse)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameRingLaws (negativeF negativeData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "poleSource" => GaussianGammaEulerReciprocalInverse.source

private theorem recover_inverse (f : PR 2) (x z R D a d N : PTm n)
    (h : Γ ⊢[PRAAx] poleSource z R D a d N) (hf : Γ ⊢[PRAAx] pointCN f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (E (negativeF f)) qF
      (exponentialInputData (negativeF f) (negativeData x)) (qData z D N)) :
    Γ ⊢[PRAAx] crossEquivalent (E f) eulerF (exponentialInputData f x) (eulerData z R D d N) := by
  let W := U f x
  let u := ed W x
  let v := ed W (negativeData x)
  let q := qData z D N
  let F := E f
  let G := E (negativeF f)
  have hi := exponential_input f x hf
  have hn := GaussianExponentialInverse.negative_input f W x hi
  have rf := GaussianRadiusExponentialName.name_regular f W x hi
  have rg := GaussianRadiusExponentialName.name_regular (negativeF f) W (negativeData x) hn
  have apart := (original_euler_inverse z R D a d N h).andE₁
  have radius := GaussianExponentialRadiusIndependence.same_input_cross (negativeF f) W _
    (negativeData x) hn (exponential_input _ _ hn.andE₁)
  have eq := cross_trans _ _ _ _ _ _ radius he
  have exchange := GaussianNameRingLaws.multiply_commutative G F v u rg rf
  have unit := GaussianExponentialInverse.exponential_inverse f W x hi
  have replace := GaussianGammaAdjacentCutoff.multiply_cross qF G F F q v u u apart.andE₁ rg rf rf
    (cross_symm _ _ _ _ eq) (cross_refl _ _ rf)
  have inverse := cross_trans _ _ _ _ _ _ replace
    (cross_trans _ _ _ _ _ _ exchange
      (cross_trans _ _ _ _ _ _ unit (GaussianNamedExponentialDifferenceIdentity.ones_equivalent x q)))
  exact cross_symm _ _ _ _
    (GaussianBoundedInverseApartness.reciprocal_matches_inverse qF F (eulerHeight z R D d N) q u
      apart.andE₁ rf apart.andE₂ inverse)

private theorem cutoff_positive {z R D a d N : PTm n} (h : Γ ⊢[PRAAx] poleSource z R D a d N) :
    Γ ⊢[PRAAx] le one N :=
  le_trans h.andE₁.andE₁.andE₁ (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right R R)) h.andE₂)

theorem normalized_equivalent (A B D neg R a d N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R)
    (hp : Γ ⊢[PRAAx] poleSource (native A B neg) R D a d N) :
    Γ ⊢[PRAAx] crossEquivalent (E GaussianLogGammaEulerNormalizedHead.nameF) eulerF
      (exponentialInputData GaussianLogGammaEulerNormalizedHead.nameF (GaussianLogGammaEulerNormalizedHead.data A B D neg N))
      (eulerData (native A B neg) R D d N) := by
  have hN := cutoff_positive hp
  exact recover_inverse _ _ _ _ _ _ _ _ hp (GaussianLogGammaEulerNormalizedHead.regular A B D neg N h.andE₁ hN)
    (GaussianLogGammaEulerExponentialHead.reciprocal_equivalent A B D neg R N h hN)

theorem original_equivalent (A B D neg R a d N : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R)
    (hp : Γ ⊢[PRAAx] poleSource (native A B neg) R D a d N) :
    Γ ⊢[PRAAx] crossEquivalent (E GaussianLogGammaEulerHead.nameF) eulerF
      (exponentialInputData GaussianLogGammaEulerHead.nameF (GaussianLogGammaEulerHead.data A B D neg N))
      (eulerData (native A B neg) R D d N) := by
  have hN := cutoff_positive hp
  exact recover_inverse _ _ _ _ _ _ _ _ hp (GaussianLogGammaEulerHead.regular A B D neg N h.andE₁ hN)
    (GaussianLogGammaEulerExponentialHead.original_reciprocal_equivalent A B D neg R N h hN)

theorem actual_original_log_Gamma_Euler_head_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        poleSource (native (var 0) (var 1) (var 3)) (var 4) (var 2) (var 5) (var 6) (var 7) ⟶
        crossEquivalent (E GaussianLogGammaEulerHead.nameF) eulerF
          (exponentialInputData GaussianLogGammaEulerHead.nameF
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 7)))
          (eulerData (native (var 0) (var 1) (var 3)) (var 4) (var 2) (var 6) (var 7))) :=
  closeUniv 8 (.impI (.impI (original_equivalent _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFiniteGamma
