import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaCutoffName
import IPRADerivations.Analysis.Gamma.EulerProducts.GammaMeshRobinLogBridge
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual names of the folded finite Gamma approximants

The finite polynomial head is multiplied by the original Gaussian
exponential of either `(γ−H_N)z/B` or `−(z/B)log N`.
The first exponent uses the original Euler-constant observations and
exact harmonic value. The second uses the actual harmonic-mesh logarithm
name. Both exponential radii are computed from the respective names'
zeroth observations, and the constructions retain the original
multiplication and exponential clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteApproximantName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular productF productData product_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalMetric (qnegative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logF : PR 2 := RationalGaussianNameEmbedding.nameF GammaMeshRobinLogBridge.meshLogF
def logExponentF : PR 2 := GaussianNameArithmetic.multiplyF logF constantF
def logExponentData (z B N : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData logF constantF N (qnegative (ofGaussian z B))

def exponentialInputData (f : PR 2) (x : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (GaussianNameBounds.U f x) x

def approximantF (f : PR 2) : PR 2 :=
  GaussianNameArithmetic.multiplyF constantF (GaussianRadiusExponentialName.nameF f)
def approximantData (f : PR 2) (x z B N : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData constantF (GaussianRadiusExponentialName.nameF f)
    (GaussianGammaEulerHead.run z B N) (exponentialInputData f x)

def pF : PR 2 := approximantF productF
def pData (z B N : PTm n) : PTm n := approximantData productF (productData z B N) z B N
def qF : PR 2 := approximantF logExponentF
def qData (z B N : PTm n) : PTm n := approximantData logExponentF (logExponentData z B N) z B N

theorem log_sample_at (p N : PTm n) : Γ ⊢[PRAAx]
    ap2 logF p N ≐ RationalGaussianEmbedding.embed (GammaMeshRobinLogBridge.harmonicLog N
      (GammaEulerConstantName.mesh p)) := by
  refine (RationalGaussianNameEmbedding.sample_at GammaMeshRobinLogBridge.meshLogF p N).eqTrans ?_
  ipra_congr (RationalGaussianEmbedding.embed (var 0) : PTm 1) with
    [GammaMeshRobinLogBridge.mesh_log_at (Γ := Γ) p N] using [GammaMeshRobinLogBridge.meshLogSample]

theorem log_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN logF N :=
  RationalGaussianNameEmbedding.name_regular _ _ (GammaMeshRobinLogBridge.mesh_name_regular _ hN)

theorem log_exponent_regular (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN logExponentF (logExponentData z B N) :=
  GaussianNameArithmetic.multiply_fast logF constantF _ _ (log_regular _ hN) (constant_regular _)

theorem exponential_input (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f (GaussianNameBounds.U f x) x := by
  refine .andI h ?_
  simpa only [GaussianRadiusExponentialName.boundedSamples, GaussianRootApproximationWitness.pointBounds] using
    GaussianNameBounds.all_samples_bounded f x h

theorem approximant_regular (f : PR 2) (x z B N : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN (approximantF f) (approximantData f x z B N) :=
  GaussianNameArithmetic.multiply_fast constantF (GaussianRadiusExponentialName.nameF f) _ _
    (constant_regular _) (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input f x h))

def productQuery (f : PR 2) (x p z B N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF (GaussianRadiusExponentialName.nameF f)
    (GaussianGammaEulerHead.run z B N) (exponentialInputData f x)) p

theorem approximant_at (f : PR 2) (x p z B N : PTm n) : Γ ⊢[PRAAx]
    ap2 (approximantF f) p (approximantData f x z B N) ≐ GaussianFastValueCut.recode
      (qmul (GaussianGammaEulerHead.run z B N) (GaussianRadiusExponentialName.sample f
        (GaussianNameBounds.U f x) (productQuery f x p z B N) x)) :=
  (GaussianNameArithmetic.multiply_at constantF (GaussianRadiusExponentialName.nameF f) _ _ p).eqTrans
    (GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _)))

theorem p_regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN pF (pData z B N) :=
  approximant_regular productF (productData z B N) z B N (product_regular z B N)
theorem q_regular (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN qF (qData z B N) :=
  approximant_regular logExponentF (logExponentData z B N) z B N (log_exponent_regular z B N hN)

theorem actual_folded_P_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (pointCN pF (pData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (p_regular _ _ _)
theorem actual_folded_Q_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ pointCN qF (qData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (q_regular _ _ _ Prf.hyp0))

theorem actual_folded_approximant_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 (approximantF f) (var 1) (approximantData f (var 0) (var 2) (var 3) (var 4)) ≐
      GaussianFastValueCut.recode (qmul (GaussianGammaEulerHead.run (var 2) (var 3) (var 4))
        (GaussianRadiusExponentialName.sample f (GaussianNameBounds.U f (var 0))
          (productQuery f (var 0) (var 1) (var 2) (var 3) (var 4)) (var 0)))) :=
  closeUniv 5 (approximant_at f _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteApproximantName
