import IPRADerivations.Analysis.Stirling.GaussianStirlingOddLogBrackets
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsOrder

/-!
# Explicit rational bounds for the original logarithm at three

The lower endpoint uses a rational below the first three odd terms at one half.
The upper endpoint is the geometric bound at cutoff zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLogThree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv Pv L_zero L_succ P_zero P_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Un Ud Nz_zero Nz_succ)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction logF name_regular)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingOddGrid (parameter gap numerator denominator denominator_positive)
open GaussianStirlingOddLogBrackets (logLower logUpper original_log_brackets upper_denominator_positive)
open RationalArgmin (rationalLE)
open RationalValueBounds (upper_congr upper_order_left upper_order_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logData : PTm n := GaussianStirlingDifference.logData one two
def lower : PTm n := fraction (num 12) (num 11)
def upper : PTm n := fraction (num 4) (num 3)

private theorem lower_cleared : Γ ⊢[PRAAx]
    numerator one (num 3) two*num 11 ≐ denominator one (num 3) two*num 12+num 13*num 32*num 32 := by
  let s : PTm n := parameter one two
  have eN0 := natEq (Nz_zero (Γ := Γ) two s)
  have eN1 := natEq (Nz_succ (Γ := Γ) zero two s)
  have eN2 := natEq (Nz_succ (Γ := Γ) one two s)
  have eN3 := natEq (Nz_succ (Γ := Γ) two two s)
  have eL0 := natEq (L_zero (Γ := Γ) zero)
  have eL1 := natEq (L_succ (Γ := Γ) zero zero)
  have eL2 := natEq (L_succ (Γ := Γ) one zero)
  have eL3 := natEq (L_succ (Γ := Γ) two zero)
  have eP0 := natEq (P_zero (Γ := Γ) two)
  have eP1 := natEq (P_succ (Γ := Γ) zero two)
  have eP2 := natEq (P_succ (Γ := Γ) one two)
  have eQ0 := natEq (P_zero (Γ := Γ) s)
  have eQ1 := natEq (P_succ (Γ := Γ) zero s)
  have eQ2 := natEq (P_succ (Γ := Γ) one s)
  have eQ3 := natEq (P_succ (Γ := Γ) two s)
  change Γ ⊢[PRAAx] Nz (succ two) two s*num 11 ≐ (Lv (succ two) zero*Pv (succ two) s)*num 12+num 13*num 32*num 32
  apply deriveNat
  ipra_simps
  rw [eN3, eN2, eN1, eN0, eL3, eL2, eL1, eL0, eP2, eP1, eP0, eQ3, eQ2, eQ1, eQ0]
  dsimp only [s, parameter]
  ipra_simps
  ring

private theorem upper_cleared : Γ ⊢[PRAAx]
    num 3*Un zero two (parameter one two) (gap one two) ≐
      num 4*Ud zero two (parameter one two) (gap one two) := by
  let s : PTm n := parameter one two
  let w : PTm n := gap one two
  have eN := natEq (Nz_zero (Γ := Γ) two s)
  have eL := natEq (L_zero (Γ := Γ) zero)
  have eP := natEq (P_zero (Γ := Γ) two)
  have eQ := natEq (P_zero (Γ := Γ) s)
  change Γ ⊢[PRAAx] num 3*(Nz zero two s*succ (two*zero)*w+two*Pv zero two*(s*s)*Lv zero zero) ≐
    num 4*(succ (two*zero)*w*(Lv zero zero*Pv zero s))
  apply deriveNat
  ipra_simps
  rw [eN, eL, eP, eQ]
  dsimp only [s, w, parameter, gap]
  ipra_simps
  ring

theorem lower_order : Γ ⊢[PRAAx] realOrder constantF logF (lower : PTm n) logData := by
  have reg := name_regular (Γ := Γ) (one+two) one (.andI (le_add_right _ _) (le_refl one))
  apply order_from_envelope _ _ _ _ one (constant_regular _) reg
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have h11 : Δ ⊢[PRAAx] le one (num 11) := by ipra_le 10
  have cmp := GaussianEuclideanDistanceName.fraction_order (Γ := Δ) (num 12) (num 11)
    (numerator one (num 3) two) (denominator one (num 3) two) h11
    (denominator_positive one (num 3) two (le_refl one))
    (le_of_eq_add lower_cleared)
  have tr := upper_order_left
    (GaussianEuclideanDistanceName.fraction (num 12) (num 11)) (logLower one two (num 3))
    (fstT (ap2 logF p logData)) one (unit p) cmp
    (original_log_brackets (Γ := Δ) one two (num 3) p (le_refl one)).andE₁
  have point := (congrFst (constant_at (Γ := Δ) p lower)).eqTrans
    (fraction_real_part (num 12) (num 11) h11)
  have h : Δ ⊢[PRAAx] RationalValueBounds.upper (fstT (ap2 constantF p lower))
      (fstT (ap2 logF p logData)) one (unit p) :=
    upper_congr point.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) tr
  simpa only [GaussianNamedRealOrderEnvelope.envelope, Syn.shift, lower, logData,
    GaussianStirlingDifference.logData, GaussianPositiveRationalLogarithm.subst_data,
    GaussianPositiveRationalLogarithm.subst_fraction, PTm.subst_num, PTm.subst_add,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using h

theorem upper_order : Γ ⊢[PRAAx] realOrder logF constantF (logData : PTm n) upper := by
  have reg := name_regular (Γ := Γ) (one+two) one (.andI (le_add_right _ _) (le_refl one))
  apply order_from_envelope _ _ _ _ one reg (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have h3 : Δ ⊢[PRAAx] le one (num 3) := by ipra_le 2
  have cmp : Δ ⊢[PRAAx] rationalLE (logUpper one two zero) (GaussianEuclideanDistanceName.fraction (num 4) (num 3)) :=
    GaussianEuclideanDistanceName.fraction_order _ _ _ _ (upper_denominator_positive one two zero (le_refl one)) h3
      (le_of_eq_add (d := zero) (upper_cleared.eqSymm.eqTrans (add_zero _).eqSymm))
  have tr := upper_order_right (fstT (ap2 logF p logData)) (logUpper one two zero)
    (GaussianEuclideanDistanceName.fraction (num 4) (num 3)) one (unit p)
    (original_log_brackets (Γ := Δ) one two zero p (le_refl one)).andE₂ cmp
  have point := (congrFst (constant_at (Γ := Δ) p upper)).eqTrans (fraction_real_part (num 4) (num 3) h3)
  have h : Δ ⊢[PRAAx] RationalValueBounds.upper (fstT (ap2 logF p logData))
      (fstT (ap2 constantF p upper)) one (unit p) :=
    upper_congr (.eqRefl _) point.eqSymm (.eqRefl _) (.eqRefl _) tr
  simpa only [GaussianNamedRealOrderEnvelope.envelope, Syn.shift, upper, logData,
    GaussianStirlingDifference.logData, GaussianPositiveRationalLogarithm.subst_data,
    GaussianPositiveRationalLogarithm.subst_fraction, PTm.subst_num, PTm.subst_add,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using h

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLogThree
