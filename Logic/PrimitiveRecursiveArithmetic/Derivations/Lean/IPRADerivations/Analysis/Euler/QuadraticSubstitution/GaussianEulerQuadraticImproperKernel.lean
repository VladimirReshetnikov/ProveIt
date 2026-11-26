import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerQuadraticImproperJacobian
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareFactorCompact
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareFactorInverse

/-!
# The actual improper quadratic Euler kernel

The sampler uses the unfactored compact kernel on the cofinal rational
cutoffs. Multiplication by the actual inverse factor transports the
Jacobian cutoff rate, and the cutoff precision pays its fixed bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerQuadraticCutoffGeometry (width)
open GaussianEulerQuadraticImproperSchedule (threshold index)
open GaussianEulerQuadraticCutoffComparison (jacobianData gain denominator)
open GaussianEulerSquareFactorInverse (inverseFactorF inverseFactorData)
open GaussianEulerQuadraticUpperEndpoint (preimage)
open GaussianGammaIntegralCutoffs (etaDen)
open GaussianEulerQuadraticImproperJacobian (reader reader_at observation_budget)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Kernel" => GaussianEulerQuadraticKernelCompactName.nameF
local notation "Jacobian" => GaussianEulerSquareJacobianCompactName.nameF
local notation "Euler" => GaussianEulerImproperName.nameF

abbrev data (z R B A c d : PTm n) : PTm n := GaussianEulerQuadraticImproperJacobian.data z R B A c d
abbrev source (z R B A c d : PTm n) : Fm PTm n := GaussianEulerQuadraticCutoffGeometry.source z R B A c d
def invBound (z B c d : PTm n) : PTm n := GaussianNameBounds.U inverseFactorF (inverseFactorData z B c d)
def kernelData (j z R B A c d : PTm n) : PTm n :=
  GaussianEulerQuadraticKernelCompactName.data z R B c d one (width j A R d) (etaDen j A R) (preimage j A R d)
def sample (p z R B A c d : PTm n) : PTm n :=
  ap2 Kernel (succ p) (kernelData (index p A (invBound z B c d) c d) z R B A c d)
abbrev referenceF : PR 2 := multiplyF inverseFactorF Euler
def referenceData (z R B A c d : PTm n) : PTm n :=
  multiplyData inverseFactorF Euler (inverseFactorData z B c d) (GaussianEulerImproperName.data z R B A)

@[simp] theorem subst_kernelData {m : ℕ} (σ : Fin n → PTm m) (j z R B A c d : PTm n) :
    Syn.subst σ (kernelData j z R B A c d) = kernelData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [kernelData,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A c d : PTm n) :
    Syn.subst σ (sample p z R B A c d) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [sample,invBound]
@[simp] theorem subst_referenceData {m : ℕ} (σ : Fin n → PTm m) (z R B A c d : PTm n) :
    Syn.subst σ (referenceData z R B A c d) = referenceData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [referenceData]

private def body : PTm 7 := sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
def nameF : PR 2 := PTm.toPR (reader body (var 0) (var 1))

theorem name_at (p z R B A c d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A c d) ≐ sample p z R B A c d := by
  have decode : Syn.subst (![p,z,R,B,A,c,d] : Fin 7 → PTm n) body = sample p z R B A c d := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  simpa only [nameF,decode] using reader_at body p z R B A c d

private theorem constant_source (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c d :=
  .andI hs.andE₁.andE₁.andE₂.andE₁.andE₁ hs.andE₂

private theorem all_samples (F : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound F x (GaussianNameBounds.U F x) := by
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRootApproximationWitness.pointBounds] using
    GaussianNameBounds.all_samples_bounded F x h

theorem original_kernel_cutoff_rate (k j z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d)
    (hj : Γ ⊢[PRAAx] le (GaussianEulerQuadraticLowerEndpoint.minimumIndex k c d) j) : Γ ⊢[PRAAx]
    independentRate Kernel referenceF (kernelData j z R B A c d) (referenceData z R B A c d)
      (invBound z B c d*gain k j A R) (denominator k j A R) := by
  let v := inverseFactorData z B c d
  let x := jacobianData j z R B A c d
  let y := GaussianEulerImproperName.data z R B A
  let w := kernelData j z R B A c d
  let a := width j A R d
  let b := etaDen j A R
  let t := preimage j A R d
  have hc := constant_source z R B A c d hs
  have interval := GaussianEulerQuadraticCutoffGeometry.original_interval_source j z R B A c d hs
  have hOriginal : Γ ⊢[PRAAx] GaussianEulerSquareFactorCompact.source z R B c d one a b t := .andI interval hs.andE₂
  have hv := GaussianEulerSquareFactorInverse.inverse_regular z B c d hc
  have hx := GaussianEulerSquareJacobianCompactName.name_regular z R B c d one a b t hOriginal
  have hy := GaussianEulerImproperName.name_regular z R B A
    (GaussianEulerIntegralGammaIdentification.improper_source z R B A hs.andE₁)
  have hw := GaussianEulerQuadraticKernelCompactName.name_regular z R B c d one a b t hOriginal
  have reduce := GaussianEulerSquareFactorInverse.cancel Jacobian Kernel x w z B c d hc hx hw
    (GaussianEulerSquareFactorCompact.original_compact_cross z R B c d one a b t hOriginal)
  have hd : Γ ⊢[PRAAx] le one (denominator k j A R) := positive_product _ _ (unit_positive _) (unit_positive _)
  have scaled := GaussianNamedMultiplyRate.independent_rate inverseFactorF Jacobian inverseFactorF Euler
    v x v y zero one (gain k j A R) (denominator k j A R)
    (GaussianNameBounds.U Jacobian x) (invBound z B c d) (le_refl one) hd hv hx hv hy
    (all_samples Jacobian x hx) (all_samples inverseFactorF v hv) (GaussianNamedDifferenceRate.self_rate _ _ hv)
    (GaussianEulerQuadraticCutoffComparison.original_jacobian_cutoff_rate k j z R B A c d hs hj)
  have exactRate := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (invBound z B c d*gain k j A R) (denominator k j A R)
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring) (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) scaled
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd exactRate reduce
    (cross_refl _ _ (multiply_fast inverseFactorF Euler v y hv hy))

theorem original_observations (p q z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A c d)) (ap2 referenceF q (referenceData z R B A c d))
      (unit p+unit q) (unit p*unit q) := by
  let M := invBound z B c d
  let k := threshold p A M
  let j := index p A M c d
  have r := original_kernel_cutoff_rate k j z R B A c d hs (le_refl j)
  have hd : Γ ⊢[PRAAx] le one (denominator k j A R) := positive_product _ _ (unit_positive _) (unit_positive _)
  exact distance_congr (name_at p z R B A c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ hd)
      (positive_product _ _ (unit_positive p) (unit_positive q))
      (observation_budget _ _ p q (GaussianEulerQuadraticImproperSchedule.cutoff_budget p A R M c d))
      (rate_at _ _ _ _ _ _ (succ p) q r))

theorem original_Euler_cross (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF referenceF (data z R B A c d) (referenceData z R B A c d) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) (sh c) (sh d) :=
    by simpa only [Fm.shift,Syn.shift,source,GaussianEulerQuadraticCutoffGeometry.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerIncompleteName.subst_data,subst_referenceData,Syn.shift,sh] using
    original_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) (sh c) (sh d) h

theorem name_regular (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B A c d) := by
  have e := original_Euler_cross z R B A c d hs
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem actual_improper_quadratic_kernel_Euler_cross_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent nameF referenceF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (referenceData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_Euler_cross _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperKernel
