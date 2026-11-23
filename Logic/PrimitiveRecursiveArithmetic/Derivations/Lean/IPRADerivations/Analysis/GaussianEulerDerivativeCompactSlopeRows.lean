import IPRADerivations.Analysis.GaussianEulerDerivativeCompactSlopeBinding
import IPRADerivations.Analysis.GaussianEulerLogarithmicPathCompactRows

/-!
# Original compact slope samples as finite telescope rows

The common physical interval is the original interval for both numerical
logarithmic orders. The existing actual packed path sampler is read at
order j+1, while the comparison value is the unchanged original improper
base observation. Every bounded row follows from the original parameter
continuity source, with both requested observations independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCompactSlopeRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicPathCompactRows (body fixedData body_at)
open GaussianEulerDerivativeCommonInterval (intervalWidth intervalDen intervalTop compactData)
open GaussianEulerDerivativeCompactSlopeBinding (gain)
open GaussianRationalParameterTelescope (slopeRows)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (u j z R B A h D N : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicContinuity.source u (succ j) z R B A h D ⋏ le one N
def slopeData (q r s j z R B A h D N : PTm n) : PTm n :=
  fixedData q (succ j) z R B h D N one (intervalWidth r s j R A) (intervalDen r s j R A) (intervalTop r s j R A)
def baseSlope (v j z R B A : PTm n) : PTm n :=
  ap2 GaussianEulerLogarithmicImproperName.nameF v (GaussianEulerLogarithmicImproperName.data (succ j) z R B A)
def numerator (q v s u : PTm n) : PTm n :=
  rateNumerator (gain s u) (GaussianEulerDerivativeCompactSlopeBinding.denominator s u) q v
def denominator (q v s u : PTm n) : PTm n :=
  rateDenominator (GaussianEulerDerivativeCompactSlopeBinding.denominator s u) q v

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (u j z R B A h D N : PTm n) :
    (source u j z R B A h D N).subst σ = source (Syn.subst σ u) (Syn.subst σ j) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_slopeData {m : ℕ} (σ : Fin n → PTm m) (q r s j z R B A h D N : PTm n) :
    Syn.subst σ (slopeData q r s j z R B A h D N) = slopeData (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ s)
      (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ h)
      (Syn.subst σ D) (Syn.subst σ N) := by simp [slopeData]
@[simp] theorem subst_baseSlope {m : ℕ} (σ : Fin n → PTm m) (v j z R B A : PTm n) :
    Syn.subst σ (baseSlope v j z R B A) = baseSlope (Syn.subst σ v) (Syn.subst σ j) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [baseSlope]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (q v s u : PTm n) :
    Syn.subst σ (numerator q v s u) = numerator (Syn.subst σ q) (Syn.subst σ v) (Syn.subst σ s) (Syn.subst σ u) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q v s u : PTm n) :
    Syn.subst σ (denominator q v s u) = denominator (Syn.subst σ q) (Syn.subst σ v) (Syn.subst σ s) (Syn.subst σ u) := by simp [denominator]

theorem denominator_positive (q v s u : PTm n) : Γ ⊢[PRAAx] le one (denominator q v s u) :=
  GaussianNamedInverseRate.denominator_positive _ q v (GaussianEulerDerivativeCompactSlopeBinding.denominator_positive s u)

theorem sample_at (i q r s j z R B A h D N : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (slopeData q r s j z R B A h D N) ≐
      ap2 GaussianEulerLogarithmicIntervalName.nameF q (compactData r s j (succ j) z R B A h D N i) :=
  body_at i q (succ j) z R B h D N one (intervalWidth r s j R A) (intervalDen r s j R A) (intervalTop r s j R A)

theorem row_source (i u j z R B A h D N : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianEulerDerivativeCompactSlopeBinding.source u j z R B A h D N i :=
  .andI hs.andE₁ (.andI hs.andE₂ (le_of_lt hi))

theorem row_bound (i q v r s u j z R B A h D N : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 body i (slopeData q r s j z R B A h D N)) (baseSlope v j z R B A)
      (numerator q v s u) (denominator q v s u) :=
  distance_congr (sample_at i q r s j z R B A h D N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerDerivativeCompactSlopeBinding.original_observations q v r s u j z R B A h D N i
      (row_source i u j z R B A h D N hs hi))

/-- The actual finite slope-row predicate has no remaining local rate or
output premise, and retains the original compact and improper queries. -/
theorem original_slope_rows (q v r s u j z R B A h D N : PTm n)
    (hs : Γ ⊢[PRAAx] source u j z R B A h D N) : Γ ⊢[PRAAx]
    slopeRows body N (slopeData q r s j z R B A h D N) (baseSlope v j z R B A)
      (numerator q v s u) (denominator q v s u) := by
  let sh (x : PTm n) := Syn.shift x
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh u) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) :=
    by simpa only [Fm.shift,subst_source,Syn.shift,sh] using hs.shift
  refine .allI (.impI ?_)
  simpa [slopeRows,GaussianRationalRiemannRefinement.termsDistance,Syn.shift,sh] using
    row_bound (var 0) (sh q) (sh v) (sh r) (sh s) (sh u) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) hh.wk Prf.hyp0

theorem actual_original_compact_path_slope_telescope_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      slopeRows body (var 12) (slopeData (var 0) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (baseSlope (var 1) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 0) (var 1) (var 3) (var 4)) (denominator (var 0) (var 1) (var 3) (var 4))) :=
  closeUniv 13 (.impI (original_slope_rows _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeCompactSlopeRows
