import IPRADerivations.Analysis.GaussianGammaRationalRatioBinding

/-!
# The original Gamma quotient at two rational shifts

For base a/b and positive endpoints c/b, d/b, exponentiate
log Γ(c/b) − (log Γ(d/b) + ((c−d)/b) log(a/b)).
Multiplication by Γ(d/b)(a/b)^((c−d)/b) recovers Γ(c/b).
This presentation allows signed shifts and either endpoint order.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (qsub)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular gammaData gamma_regular)
open GaussianStirlingLogDuplication (exponential_regular exponential_gamma exponential_sum)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "P" => logGammaF
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def coefficient (b c d : PTm n) : PTm n := qsub (fraction c b) (fraction d b)

def powerLogF : PR 2 := multiplyF constantF H
def powerLogData (a b c d : PTm n) : PTm n := multiplyData constantF H (coefficient b c d) (hd a b)

def denominatorLogF : PR 2 := addF P powerLogF
def denominatorLogData (a b c d : PTm n) : PTm n := addData (logGammaData d b) (powerLogData a b c d)

def quotientLogF : PR 2 := GaussianNamedDifference.nameF P denominatorLogF
def quotientLogData (a b c d : PTm n) : PTm n :=
  GaussianNamedDifference.data (logGammaData c b) (denominatorLogData a b c d)

def powerF : PR 2 := E powerLogF
def powerData (a b c d : PTm n) : PTm n := ed powerLogF (powerLogData a b c d)
def denominatorF : PR 2 := multiplyF G powerF
def denominatorData (a b c d : PTm n) : PTm n :=
  multiplyData G powerF (gammaData d b) (powerData a b c d)
def quotientF : PR 2 := E quotientLogF
def quotientData (a b c d : PTm n) : PTm n := ed quotientLogF (quotientLogData a b c d)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (b c d : PTm n) :
    Syn.subst σ (coefficient b c d) = coefficient (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [coefficient]

@[simp] theorem subst_powerLogData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (powerLogData a b c d) = powerLogData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [powerLogData]

@[simp] theorem subst_denominatorLogData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (denominatorLogData a b c d) =
      denominatorLogData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [denominatorLogData]

@[simp] theorem subst_quotientLogData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (quotientLogData a b c d) =
      quotientLogData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [quotientLogData]

@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (powerData a b c d) = powerData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [powerData,GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] theorem subst_denominatorData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (denominatorData a b c d) =
      denominatorData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [denominatorData]

@[simp] theorem subst_quotientData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (quotientData a b c d) =
      quotientData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [quotientData,GaussianGammaFiniteApproximantName.exponentialInputData]

theorem power_log_regular (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN powerLogF (powerLogData a b c d) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianHarmonicLogarithmName.name_regular a b ha)

theorem denominator_log_regular (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] source d b) :
    Γ ⊢[PRAAx] pointCN denominatorLogF (denominatorLogData a b c d) :=
  add_fast _ _ _ _ (log_gamma_regular d b hD) (power_log_regular a b c d ha)

theorem quotient_log_regular (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b) :
    Γ ⊢[PRAAx] pointCN quotientLogF (quotientLogData a b c d) :=
  GaussianNamedDifference.name_regular _ _ _ _ (log_gamma_regular c b hc) (denominator_log_regular a b c d ha hD)

theorem denominator_exponential (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] source d b) :
    Γ ⊢[PRAAx] crossEquivalent denominatorF (E denominatorLogF) (denominatorData a b c d)
      (ed denominatorLogF (denominatorLogData a b c d)) := by
  let z := logGammaData d b
  let p := powerLogData a b c d
  have hz := log_gamma_regular d b hD
  have hp := power_log_regular a b c d ha
  have hpower := exponential_regular powerLogF p hp
  have factors := GaussianGammaAdjacentCutoff.multiply_cross G (E P) powerF powerF (gammaData d b) (ed P z)
    (powerData a b c d) (powerData a b c d) (gamma_regular d b hD) (exponential_regular P z hz)
    hpower hpower (cross_symm _ _ _ _ (exponential_gamma d b hD)) (cross_refl _ _ hpower)
  exact cross_trans _ _ _ _ _ _ factors (exponential_sum P powerLogF z p hz hp)

theorem quotient_balance (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF quotientF denominatorF) G
      (multiplyData quotientF denominatorF (quotientData a b c d) (denominatorData a b c d)) (gammaData c b) := by
  let x := quotientLogData a b c d
  let y := denominatorLogData a b c d
  let z := logGammaData c b
  have hy := denominator_log_regular a b c d ha hD
  have hz := log_gamma_regular c b hc
  have hx := quotient_log_regular a b c d ha hc hD
  have hq := exponential_regular quotientLogF x hx
  have hDen := multiply_fast _ _ _ _ (gamma_regular d b hD) (exponential_regular powerLogF _ (power_log_regular a b c d ha))
  have denominators := denominator_exponential a b c d ha hD
  have factors := GaussianGammaAdjacentCutoff.multiply_cross quotientF quotientF denominatorF (E denominatorLogF)
    (quotientData a b c d) (quotientData a b c d) (denominatorData a b c d) (ed denominatorLogF y)
    hq hq hDen (exponential_regular denominatorLogF y hy) (cross_refl _ _ hq) denominators
  have balance := GaussianGammaRationalRatioBinding.difference_add_recover P denominatorLogF z y hz hy
  let U (f : PR 2) (v : PTm n) := GaussianNameBounds.U f v
  have EBalance := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent quotientLogF denominatorLogF P
    (U quotientLogF x) (U denominatorLogF y) (U P z) x y z
    (GaussianGammaFiniteApproximantName.exponential_input _ _ hx) (GaussianGammaFiniteApproximantName.exponential_input _ _ hy)
    (GaussianGammaFiniteApproximantName.exponential_input _ _ hz) balance
  exact cross_trans _ _ _ _ _ _ factors (cross_trans _ _ _ _ _ _ EBalance (exponential_gamma c b hc))

theorem actual_original_Gamma_two_shift_quotient_binding_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) ⟶ source (var 2) (var 1) ⟶ source (var 3) (var 1) ⟶
        crossEquivalent (multiplyF quotientF denominatorF) G
          (multiplyData quotientF denominatorF (quotientData (var 0) (var 1) (var 2) (var 3))
            (denominatorData (var 0) (var 1) (var 2) (var 3))) (gammaData (var 2) (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (quotient_balance _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftBinding
