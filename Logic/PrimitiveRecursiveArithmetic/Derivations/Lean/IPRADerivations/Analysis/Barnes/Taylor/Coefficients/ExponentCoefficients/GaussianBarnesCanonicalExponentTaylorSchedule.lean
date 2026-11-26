import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorHorner
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# Explicit finite schedules for the original Barnes exponent Taylor polynomial

The tail cutoff first pays both original cofinal logarithm errors.
The prefactor precision then pays the cost of freezing its two constants
at that fixed polynomial. The Taylor remainder retains its full order.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorSchedule

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open GaussianBarnesCanonicalExponentTaylor (nameF data)
open GaussianBarnesCanonicalCorrectedMercatorCofinal
  (input cutoff cutoff_budget analyticDenominator analytic_denominator_positive scheduledNumerator scheduledDenominator)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian evaluate qzero positive_product)
open GaussianRationalSyntheticDivision (canonicalCoefficients)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "TaylorNumerator" => GaussianBarnesCanonicalCorrectedMercator.numerator
local notation "FrozenNumerator" => GaussianBarnesCanonicalExponentTaylorFrozen.numerator
local notation "FrozenDenominator" => GaussianBarnesCanonicalExponentTaylorFrozen.denominator
local notation "FrozenCost" => GaussianBarnesCanonicalExponentTaylorFrozen.cost

def tailCutoff (p R : PTm n) : PTm n := cutoff p R

def prefactorCost (p z h R B M : PTm n) : PTm n :=
  FrozenCost z h R B
    (GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) (tailCutoff p R) M)

def precision (p z h R B M : PTm n) : PTm n := exponent (prefactorCost p z h R B M) p

def buffer (p z h R B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer (precision p z h R B M) z R B (tailCutoff p R) M

def value (p z h R B M : PTm n) : PTm n := evaluate (buffer p z h R B M) (ofGaussian h B)

def numerator (p R B H M : PTm n) : PTm n :=
  TaylorNumerator (previous M) H*unit p+two*analyticDenominator (previous M) R B

def denominator (p R B M : PTm n) : PTm n := scheduledDenominator p (previous M) R B

theorem precision_budget (p z h R B M : PTm n) :
    Γ ⊢[PRAAx] le (prefactorCost p z h R B M*unit p) (unit (precision p z h R B M)) :=
  query_budget _ _

theorem buffer_length (p z h R B M : PTm n) : Γ ⊢[PRAAx] length (buffer p z h R B M) ≐ succ (previous M) :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_length _ _ _ _ _ _

theorem buffer_zero (p z h R B M : PTm n) : Γ ⊢[PRAAx] entry (buffer p z h R B M) (previous M) ≐ qzero :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_zero _ _ _ _ _ _

theorem buffer_canonical (p z h R B M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (buffer p z h R B M) :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_canonical _ _ _ _ _ _

theorem denominator_positive (p R B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator p R B M) :=
  positive_product _ _ (unit_positive p) (analytic_denominator_positive (previous M) R B hB)

private theorem radius_comparison (p z h R B H M : PTm n) :
    let q := precision p z h R B M
    let r := tailCutoff p R
    Γ ⊢[PRAAx] le (FrozenNumerator p q z h R B H r M*denominator p R B M)
      (numerator p R B H M*FrozenDenominator p q R B M) := by
  let q := precision p z h R B M
  let D := analyticDenominator (previous M) R B
  let E := denominator p R B M
  let U := unit p
  let V := unit q
  let A := scheduledNumerator p (previous M) R B H
  have he : Γ ⊢[PRAAx] le (prefactorCost p z h R B M*U) V := precision_budget p z h R B M
  have joined := add_le_add_right (A*V*E) (mul_le_mul_right (D*E) he)
  exact le_congr (by
    dsimp only [D,E,denominator,scheduledDenominator,U,V,A,prefactorCost,
      GaussianBarnesCanonicalExponentTaylorFrozen.numerator,GaussianNamedRateComposition.leadingNumerator,q]
    ipra_ring) (by
      dsimp only [D,E,denominator,scheduledDenominator,U,V,A,numerator,GaussianBarnesCanonicalExponentTaylorFrozen.denominator,
        GaussianNamedRateComposition.leadingDenominator,scheduledNumerator,GaussianNamedRateComposition.leadingNumerator,q]
      ipra_ring) joined

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (value p z h R B M)
      (numerator p R B H M) (denominator p R B M) := by
  let q := precision p z h R B M
  let r := tailCutoff p R
  have dpos := denominator_positive p R B M hs.andE₁.andE₁
  have oldPos : Γ ⊢[PRAAx] le one (FrozenDenominator p q R B M) :=
    positive_product _ _ dpos (unit_positive q)
  have raw := GaussianBarnesCanonicalExponentTaylorHorner.rate_of_cutoff p q z h R B H r M hs (cutoff_budget p R)
  exact GaussianNamedRateRadius.weaken nameF constantF (data z h R B) (value p z h R B M)
    (FrozenNumerator p q z h R B H r M) (FrozenDenominator p q R B M) (numerator p R B H M) (denominator p R B M)
    oldPos dpos (radius_comparison p z h R B H M) raw

theorem analytic_le_one (R B H M : PTm n) (hs : Γ ⊢[PRAAx] le (num 4*H) B) :
    Γ ⊢[PRAAx] le (TaylorNumerator (previous M) H) (analyticDenominator (previous M) R B) := by
  let j := succ (previous M)
  have hH : Γ ⊢[PRAAx] le (two*H) B :=
    le_trans (le_of_eq_add (d := two*H) (by ipra_ring)) hs
  have power := pw_le_pw j hH
  have hj : Γ ⊢[PRAAx] le two j :=
    le_trans (LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ M)) (le_succ_self _)
  have first := le_mul_mono hj power
  have last := le_mul_mono (le_refl (j*pw B j)) (initial_positive (Γ := Γ) R)
  exact le_trans first (le_congr (LeanProofs.IPRA.Common.mul_one_right _) (.eqRefl _) last)

theorem radius_le_three (p R B H M : PTm n) (hs : Γ ⊢[PRAAx] le (num 4*H) B) :
    Γ ⊢[PRAAx] le (numerator p R B H M) (num 3*denominator p R B M) := by
  let D := analyticDenominator (previous M) R B
  have first := mul_le_mul_right (unit p) (analytic_le_one R B H M hs)
  have last := mul_le_mul_right (two*D) (unit_positive (Γ := Γ) p)
  exact le_congr (by unfold numerator; ipra_ring) (by unfold denominator scheduledDenominator; ipra_ring)
    (add_le_add₂ first (le_congr (one_mul _) (.eqRefl _) last))

theorem actual_Barnes_scheduled_exponent_Horner_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     input (previous M) z h R B H ⟶ independentRate nameF constantF (data z h R B) (value p z h R B M)
       (numerator p R B H M) (denominator p R B M)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorSchedule
