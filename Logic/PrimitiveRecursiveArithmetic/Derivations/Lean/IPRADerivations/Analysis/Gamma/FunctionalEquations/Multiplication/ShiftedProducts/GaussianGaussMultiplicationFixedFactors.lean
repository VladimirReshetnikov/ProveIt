import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Cutoffs.GaussianGaussEulerCutoffUniform
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.Limits.GaussianGaussMultiplicationCofinalRows

/-!
# Uniform bounds for the remaining fixed Gauss factors

The finite powers and both fixed-cutoff Euler names have usable bounds
at every observation clock. Their bounds are independent of the finite
cutoff parameter.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationFixedFactors

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianGaussMultiplicationPowerRate (powerF exponentF exponentData rowLogData row_power_input)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameBounds (U)
open GaussianRationalMetric (bounded)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "needed" => GaussianGammaEulerInverseApproximationName.cutoff

def scaledEulerData (z R B m d N : PTm n) : PTm n :=
  eulerData (scale m z) (scaledRadius R m) B d (GaussianGammaGaussEulerHeads.cutoff m N)
def unitEulerData (m N : PTm n) : PTm n :=
  eulerData oneCode one one one (GaussianGammaGaussEulerHeads.cutoff m N)
def eulerBound (z R B d : PTm n) : PTm n := num 3+U gammaF (gammaData z R B d)
def scaledBound (z R B m d : PTm n) : PTm n := eulerBound (scale m z) (scaledRadius R m) B d
def unitBound : PTm n := eulerBound oneCode one one one
def powerBound (R m : PTm n) : PTm n :=
  GaussianRadiusExponentialLipschitzRate.factor (GaussianGaussMultiplicationPowerRate.radius R m)

ipra_subst scaledEulerData
ipra_subst unitEulerData [one]
ipra_subst eulerBound
ipra_subst scaledBound
@[simp] theorem subst_unitBound {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (unitBound : PTm n) = unitBound :=
  by simp [unitBound,one]
ipra_subst powerBound

theorem euler_bound_at (s p z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hn : Γ ⊢[PRAAx] le (needed s R a d) N) :
    Γ ⊢[PRAAx] bounded (ap2 eulerF p (eulerData z R B d N)) (eulerBound z R B d) one := by
  have cs := GaussianGaussEulerCutoffUniform.uniform_error s p z R B a d N h hn
  have cb := GaussianNameBounds.sample_bound gammaF (gammaData z R B d) p
    (GaussianGammaReciprocalInverse.gamma_regular z R B a d h)
  exact GaussianRationalDistanceOrder.norm_from_distance_same (le_refl one) cs cb

theorem euler_bounds (s z R B a d N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B a d)
    (hn : Γ ⊢[PRAAx] le (needed s R a d) N) :
    Γ ⊢[PRAAx] pointBounds eulerF (eulerBound z R B d) (eulerData z R B d N) := by
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaReciprocalInverse.source (sh z) (sh R) (sh B) (sh a) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (needed (sh s) (sh R) (sh a) (sh d)) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using hn.shift
  simpa [pointBounds,Syn.shift,sh] using euler_bound_at (sh s) (var 0) (sh z) (sh R) (sh B) (sh a) (sh d) (sh N) hs ns

private theorem power_input (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (GaussianGaussMultiplicationPowerRate.radius R m)
      (exponentData z R B m (rowLogData m N)) :=
  row_power_input z R B m N h.andE₁.andE₁ hn h.andE₂.andE₁.andE₂.andE₁ h.andE₁.andE₂

theorem power_regular (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN powerF (rowData z R B m N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (power_input z R B m a d N h hn)

theorem power_bound_at (p z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] bounded (ap2 powerF p (rowData z R B m N)) (powerBound R m) one := by
  let W := GaussianGaussMultiplicationPowerRate.radius R m
  let x := exponentData z R B m (rowLogData m N)
  exact GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at exponentF W p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _
      (GaussianRadiusExponentialName.query_bound exponentF W x p (power_input z R B m a d N h hn)))

theorem power_bounds (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointBounds powerF (powerBound R m) (rowData z R B m N) := by
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hn.shift
  simpa [pointBounds,Syn.shift,sh] using power_bound_at (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) (sh N) hs ns

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationFixedFactors
