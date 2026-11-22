import IPRADerivations.Analysis.GaussianGammaC7Name
import IPRADerivations.Analysis.GaussianGammaCanonicalExponentBound
import IPRADerivations.Analysis.GaussianPositiveExponentialMajorant

/-!
# The C9 majorant for the original reciprocal Gamma name

Every actual observation of the C7 exponential factor, at its original
input clock and cutoff, has norm at most (3^{2R^2+2R}). The original
retimed product with the literal polynomial head consequently has the
C9 norm bound (R(1+R)^{2R}3^{2R^2+2R}) at every observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaC9Bound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (source exponentPoint exponentRadius exponentialPoint exponential_sample_at)
open GaussianGammaCanonicalExponentBound (numericalRadius exponent_point_numerical_bound)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentialMajorant (R : PTm n) : PTm n := pw (num 3) (numericalRadius R)
def majorant (R : PTm n) : PTm n := R*pw (one+R) (two*R)*exponentialMajorant R

@[simp] theorem subst_exponentialMajorant {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (exponentialMajorant R) = exponentialMajorant (Syn.subst σ R) := by simp [exponentialMajorant]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (majorant R) = majorant (Syn.subst σ R) := by simp [majorant]

theorem exponential_observation_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (exponentialPoint p z R B) (exponentialMajorant R) one := by
  let r := exponentRadius z R B
  let j := GaussianRadiusExponentialName.inputPrecision r p
  let K := GaussianRadiusExponentialName.index r p
  exact bound_congr (exponential_sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound (exponentPoint j z R B) (numericalRadius R) K
      (exponent_point_numerical_bound j z R B h))

theorem reciprocal_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (GaussianGammaC7Name.sample p z R B) (majorant R) one := by
  apply bound_congr (GaussianGammaC7Name.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
  apply (GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr
  exact bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) (GaussianGammaC7Name.head_bound z R B h)
      (exponential_observation_bound (GaussianGammaC7Name.samplePrecision p z R B) z R B h))

theorem reciprocal_name_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianRootApproximationWitness.pointBounds GaussianGammaC7Name.nameF
      (majorant R) (GaussianGammaC7Name.data z R B) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by
    simpa only [Fm.shift, Syn.shift, GaussianGammaCanonicalExponent.subst_source] using h.shift
  simpa only [GaussianRootApproximationWitness.pointBounds, GaussianGammaC7Name.sample,
    GaussianGammaC7Name.subst_data, subst_majorant, Syn.shift] using
    reciprocal_sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs

theorem original_C9_exponential_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶
      bounded (exponentialPoint (var 0) (var 1) (var 2) (var 3)) (exponentialMajorant (var 2)) one) :=
  closeUniv 4 (.impI (exponential_observation_bound _ _ _ _ Prf.hyp0))

theorem original_C9_reciprocal_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianRootApproximationWitness.pointBounds GaussianGammaC7Name.nameF
      (majorant (var 1)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (reciprocal_name_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaC9Bound
