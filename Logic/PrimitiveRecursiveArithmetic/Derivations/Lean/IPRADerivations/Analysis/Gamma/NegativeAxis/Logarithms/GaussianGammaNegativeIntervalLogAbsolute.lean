import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalGammaSign
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication

/-!
# Logarithm of the absolute original Gamma on a negative interval

At x = -N-1+a/b with 0 < a < b, the original shift product has
absolute value c/d. The log-absolute name adds the positive log-Gamma
at 1+a/b to the original rational logarithm of d/c. Its named
exponential recovers the original sign-adjusted Gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsolute

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianFactorBudget (power_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (productNumerator productDenominator lowerDenominator
  signedF signedData inversePoint terminalData signed_gamma_identity signed_gamma_source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveLogarithmScale (sum_axis exact_rational_axis)
open GaussianRationalHorner (positive_product)
open GaussianRealNameExponentialInjectivity (axisSamples)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular log_gamma_axis gamma_regular)
open GaussianStirlingLogDuplication (exponential_sum exponential_gamma exponential_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "ld" => GaussianPositiveRationalLogarithm.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def inverseLogData (a b N : PTm n) : PTm n :=
  ld (productDenominator b N) (productNumerator a b N)

def nameF : PR 2 := addF logGammaF L
def nameData (a b N : PTm n) : PTm n := addData (logGammaData (b+a) b) (inverseLogData a b N)
def expF : PR 2 := E nameF
def expData (a b N : PTm n) : PTm n := ed nameF (nameData a b N)

ipra_subst inverseLogData [productNumerator, productDenominator]

ipra_subst nameData

ipra_subst expData [exponentialInputData]

theorem terminal_source (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (b+a) b := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  exact .andI (le_trans hb (le_add_right _ _)) hb

theorem inverse_source (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (productDenominator b N) (productNumerator a b N) := by
  have hb := (terminal_source a b h).andE₂
  have lower := (signed_gamma_source a b N h).andE₂.andE₁
  have factor : Γ ⊢[PRAAx] le one (productNumerator a b N*GaussianStirlingGammaLogarithm.gammaMargin) :=
    le_congr (.eqRefl _) (mul_comm _ _) lower
  exact .andI (positive_product _ _ (power_positive b (succ N) hb) hb)
    (GaussianDominantScalarOrder.factor_positive_left _ _ factor)

theorem name_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN nameF (nameData a b N) :=
  add_fast logGammaF L (logGammaData (b+a) b) (inverseLogData a b N)
    (log_gamma_regular _ _ (terminal_source a b h))
    (GaussianPositiveRationalLogarithm.name_regular _ _ (inverse_source a b N h))

theorem name_axis (a b N : PTm n) : Γ ⊢[PRAAx] axisSamples nameF (nameData a b N) :=
  sum_axis logGammaF L (logGammaData (b+a) b) (inverseLogData a b N)
    (log_gamma_axis _ _) (exact_rational_axis _ _)

theorem name_real (a b N : PTm n) : Γ ⊢[PRAAx] realSamples nameF (nameData a b N) := by
  refine .allI ?_
  let A := Syn.shift a
  let B := Syn.shift b
  let J := Syn.shift N
  let p : PTm (n+1) := var 0
  have c : Γ.map Fm.shift ⊢[PRAAx]
      GaussianRationalHorner.canonical (ap2 nameF p (nameData A B J)) :=
    GaussianNameArithmetic.add_canonical logGammaF L (logGammaData (B+A) B) (inverseLogData A B J) p
  have r := GaussianRealNameExponentialInjectivity.axis_sample_at nameF (nameData A B J) p
    (name_axis (Γ := Γ.map Fm.shift) A B J)
  simpa only [realSamples,subst_nameData,Syn.shift,A,B,J,p] using Prf.andI c r

theorem exp_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN expF (expData a b N) :=
  exponential_regular nameF (nameData a b N) (name_regular a b N h)

theorem original_exponential (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent expF signedF (expData a b N) (signedData a b N) := by
  let d := productDenominator b N
  let c := productNumerator a b N
  let x := logGammaData (b+a) b
  let y := inverseLogData a b N
  let u := terminalData a b
  let v := inversePoint a b N
  have ht := terminal_source a b h
  have hi := inverse_source a b N h
  have hx := log_gamma_regular _ _ ht
  have hy : Γ ⊢[PRAAx] pointCN L y := GaussianPositiveRationalLogarithm.name_regular d c hi
  have hu : Γ ⊢[PRAAx] pointCN gammaF u := gamma_regular _ _ ht
  have hv := constant_regular (Γ := Γ) v
  have split := exponential_sum logGammaF L x y hx hy
  have factors := multiply_cross (E logGammaF) gammaF (E L) constantF (ed logGammaF x) u (ed L y) v
    (exponential_regular logGammaF x hx) hu (exponential_regular L y hy) hv
    (exponential_gamma (b+a) b ht) (GaussianPositiveRationalLogarithm.exponential_fraction d c hi)
  have commute := GaussianNameRingLaws.multiply_commutative gammaF constantF u v hu hv
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ factors
      (cross_trans _ _ _ _ _ _ commute (cross_symm _ _ _ _ (signed_gamma_identity a b N h))))

theorem actual_original_negative_interval_log_absolute_Gamma_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        (pointCN nameF (nameData (var 0) (var 1) (var 2)) ⋏
          (realSamples nameF (nameData (var 0) (var 1) (var 2)) ⋏
            crossEquivalent expF signedF (expData (var 0) (var 1) (var 2)) (signedData (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (name_regular _ _ _ Prf.hyp0)
    (.andI (name_real _ _ _) (original_exponential _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsolute
