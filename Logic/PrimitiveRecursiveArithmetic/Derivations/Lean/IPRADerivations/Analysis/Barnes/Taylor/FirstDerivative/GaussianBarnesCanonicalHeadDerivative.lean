import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadDerivativeJoin
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative

/-!
# Uniform derivative quotient of the original kept Barnes head

The actual finite base powers and the actual correction exponential
supply the two independent first-order comparisons. The resulting
quotient targets the derivative of the original normalized head and
has a bound depending only on the disk and the kept cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivative

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalHead (headData)
open GaussianBarnesCanonicalHeadCorrectionExponentialDerivative
  (derivative_regular errorNumerator exponentialBound exponential_samples incrementGain)
open GaussianBarnesCanonicalHeadDerivativeJoin (derivativeF derivativeData)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponentialF
local notation "D" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivativeF
local notation "dd" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivativeData
local notation "errorGain" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.errorGain
local notation "Slope" => GaussianBarnesCanonicalHeadCorrectionDerivative.slope
local notation "Head" => GaussianBarnesCanonicalHead.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

def correctionDerivativeCap (R N : PTm n) : PTm n := exponentialBound R N*(N*(R+one))
def gain (R N : PTm n) : PTm n :=
  GaussianBarnesCanonicalHeadDerivativeJoin.gain R N (two*errorGain R N)
    (correctionDerivativeCap R N) (exponentialBound R N)

def input (z h R B N : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalHeadPolynomialDerivative.input z h R B (norm1 h) ⋏
    (le one (normSq h) ⋏ (le (norm1 h) B ⋏ le (incrementGain R N*norm1 h) B))

@[simp] theorem subst_correctionDerivativeCap {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (correctionDerivativeCap R N) = correctionDerivativeCap (Syn.subst σ R) (Syn.subst σ N) := by
  simp [correctionDerivativeCap,one]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (gain R N) = gain (Syn.subst σ R) (Syn.subst σ N) := by simp [gain,two]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B N : PTm n) :
    (input z h R B N).subst σ = input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ N) := by simp [input,one]

theorem correction_derivative_samples (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    sampleBound D (dd z B N) (correctionDerivativeCap R N) := by
  have hb : Γ ⊢[PRAAx] sampleBound constantF (Slope z B N) (N*(R+one)) := by
    refine .allI ?_
    let sh (x : PTm n) := Syn.shift x
    let Δ := Γ.map Fm.shift
    have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hB.shift
    have h : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
    have core := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.slope_bound (sh z) (sh B) (sh N) (sh R) b h
    have sample : Δ ⊢[PRAAx] bounded (ap2 constantF (var 0) (Slope (sh z) (sh B) (sh N))) (sh N*(sh R+one)) one :=
      GaussianRationalReciprocal.bound_congr (constant_at _ _).eqSymm (.eqRefl _) (.eqRefl _) core
    simpa only [sampleBound,Syn.shift,sh,Δ,GaussianBarnesCanonicalHeadCorrectionDerivative.subst_slope,
      PTm.subst_mul,PTm.subst_add,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using sample
  exact GaussianNamedBoundedProductObservation.sample_bounds F constantF (exponentData z B N) (Slope z B N) _ _
    (exponential_samples z B N R hB hz) hb

theorem correction_quotient_rate (z h R B N : PTm n) (hi : Γ ⊢[PRAAx] input z h R B N) : Γ ⊢[PRAAx]
    independentRate (QF F F) D
      (qd F F (exponentData (add z h) B N) (exponentData z B N) h B)
      (dd z B N) (two*errorGain R N*norm1 h) B := by
  let H := norm1 h
  let x := exponentData (add z h) B N
  let y := exponentData z B N
  let w := dd z B N
  have hs := hi.andE₁
  have hB := hs.andE₁
  have raw := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.rate z h B N R H hB hs.andE₂.andE₁
    hs.andE₂.andE₂.andE₂ hi.andE₂.andE₂.andE₁ hi.andE₂.andE₂.andE₂
  exact GaussianNativeDerivativeQuotientQuadratic.rate F F D x y w h B (errorGain R N)
    (GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular (add z h) B N)
    (GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular z B N)
    (derivative_regular z B N) hB hi.andE₂.andE₁ raw

theorem rate (z h R B N : PTm n) (hi : Γ ⊢[PRAAx] input z h R B N) : Γ ⊢[PRAAx]
    independentRate (QF Head Head) derivativeF
      (qd Head Head (headData (add z h) R B N) (headData z R B N) h B)
      (derivativeData z B N) (gain R N*norm1 h) B := by
  have hs := hi.andE₁
  have hB := hs.andE₁
  have hz := hs.andE₂.andE₁
  exact GaussianBarnesCanonicalHeadDerivativeJoin.rate z h R B N (two*errorGain R N)
    (correctionDerivativeCap R N) (exponentialBound R N) hs hi.andE₂.andE₁ hi.andE₂.andE₂.andE₁
    (correction_derivative_samples z R B N hB hz) (exponential_samples z B N R hB hz)
    (correction_quotient_rate z h R B N hi)

theorem actual_Barnes_original_kept_head_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let N := var 4
     input z h R B N ⟶ independentRate (QF Head Head) derivativeF
       (qd Head Head (headData (add z h) R B N) (headData z R B N) h B)
       (derivativeData z B N) (gain R N*norm1 h) B) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivative
