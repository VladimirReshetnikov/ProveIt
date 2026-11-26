import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerTaylorMajorant
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmIncrement
import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureDifference

/-!
# First-order error in the original finite Euler logarithm rows

The relative displacement of each shifted logarithm is the actual
unshifted step times the reciprocal row. The quadratic scalar majorant
sums their errors, and the original named family's count-dependent
clock pays for the per-row observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaFiniteValueProperness (fraction_equal)
open GaussianLogGammaEulerArgumentIncrement (step step_ofGaussian rowF rowBody rowData subst_rowData)
open GaussianLogGammaEulerLinearSlope (linearSum row_shifted_at sum_value)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerTaylorMajorant (rowBound rowBounds rowSquare finite_sum_bound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithmIncrementBound (input subst_input)
open GaussianRightHalfPlaneLogarithmRelativeStep (relative relative_binding denominator_positive)
open GaussianRightHalfPlaneRadialContinuity (shifted_displacement)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "sumF" => GaussianLogGammaEulerArgumentIncrement.sumF
local notation "sumData" => GaussianLogGammaEulerArgumentIncrement.sumData
local notation "linearBody" => GaussianLogGammaEulerLinearSlope.rowBody
local notation "linearData" => GaussianLogGammaEulerLinearSlope.rowData
local notation "rawNumerator" => GaussianLogGammaEulerTaylorMajorant.errorNumerator
local notation "rawDenominator" => GaussianLogGammaEulerTaylorMajorant.errorDenominator

/-- The relative displacement is the literal first-order Euler logarithm row. -/
theorem relative_row (i A B neg a b sign D : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] relative (native (A + i * D) B neg) (native (a + i * D) b sign) ≐
      inst2 linearBody i (linearData A B neg a b sign D) := by
  let u := native (A + i * D) B neg
  let v := native (a + i * D) b sign
  have hD := h.andE₂
  have hu := denominator_positive (A + i * D) B neg
    (GaussianLogGammaEulerHead.shifted_source i A D neg h).andE₁
  have move : Γ ⊢[PRAAx] step (A + i * D) B neg (a + i * D) b sign D ≐ step A B neg a b sign D :=
    (step_ofGaussian (A + i * D) B neg (a + i * D) b sign D hD).eqTrans
      ((fraction_equal _ _ D hD (shifted_displacement i A B neg a b sign D)).eqTrans
        (step_ofGaussian A B neg a b sign D hD).eqSymm)
  exact (relative_binding u v D hD hu).eqSymm.eqTrans
    ((qmul_congr move (.eqRefl _)).eqTrans (row_shifted_at i A B neg a b sign D hD).eqSymm)

private abbrev observedBody : PTm 2 := GaussianNamedFiniteSumFamily.body rowF rowBody

private def observedData (p A B neg a b sign D : PTm n) : PTm n :=
  pairT p (rowData A B neg a b sign D)

/-- The analytic estimate applies to the actual common-clock row sampler. -/
theorem row_sample_error (p i A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] distanceBounded (inst2 observedBody i (observedData p A B neg a b sign D))
      (inst2 linearBody i (linearData A B neg a b sign D))
      (num 4 * H * H * unit p + num 3 * rowSquare A D i) (rowSquare A D i * unit p) := by
  let x := rowData A B neg a b sign D
  have read := (GaussianNamedFiniteSumFamily.term_at (Γ := Γ) rowF rowBody i p x).eqTrans
    (congrAp2 rowF (.eqRefl p) (GaussianLogGammaEulerArgumentIncrement.row_at i A B neg a b sign D))
  exact distance_congr read.eqSymm (relative_row i A B neg a b sign D h.andE₁.andE₁) (.eqRefl _) (.eqRefl _)
    (GaussianRightHalfPlaneLogarithmIncrement.shifted_sample_error p i A B neg a b sign D H J M h)

private theorem row_bound (p i A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] rowBound (differenceBody observedBody linearBody)
      (pairT (observedData p A B neg a b sign D) (linearData A B neg a b sign D))
      A D (num 4 * H * H) (num 3) (unit p) i :=
  bound_congr (difference_body_at observedBody linearBody i (observedData p A B neg a b sign D)
    (linearData A B neg a b sign D)).eqSymm (.eqRefl _) (.eqRefl _)
    (row_sample_error p i A B neg a b sign D H J M h)

/-- The original finite row observations at any common clock retain the per-row allowance. -/
theorem raw_sum_error (p A B neg a b sign D H J M K N : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K * A)) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianNamedFiniteSumFamily.finite rowF rowBody p (succ N) (rowData A B neg a b sign D))
      (linearSum A B neg a b sign D N)
      (rawNumerator (num 4 * H * H) (num 3) (unit p) D K N) (rawDenominator (unit p) D) := by
  let x := observedData p A B neg a b sign D
  let y := linearData A B neg a b sign D
  let t := differenceBody observedBody linearBody
  have rows : Γ ⊢[PRAAx] rowBounds t (pairT x y) A D N (num 4 * H * H) (num 3) (unit p) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (succ (s N)) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] input (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_input] using h.shift.wk
    simpa only [Δ, s, Syn.shift, t, x, y, observedData, subst_pairT, subst_rowData,
      GaussianLogGammaEulerLinearSlope.subst_rowData, PTm.subst_mul, PTm.subst_num, subst_unit] using
      row_bound (s p) (var 0) (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) hs
  have hD := h.andE₁.andE₁.andE₂
  have hA := h.andE₁.andE₁.andE₁.andE₁
  have total := finite_sum_bound t (pairT x y) A D K N (num 4 * H * H) (num 3) (unit p)
    hA hD (unit_positive p) hK rows
  exact bound_congr (finite_sum_difference observedBody linearBody (succ N) x y) (.eqRefl _) (.eqRefl _) total

def coefficient (H K : PTm n) : PTm n := num 4 * H * H * (K * K + two)
def errorNumerator (p D H K : PTm n) : PTm n := coefficient H K * unit p + num 3 * (D * D)
def errorDenominator (p D : PTm n) : PTm n := D * D * unit p

/-- The actual finite sum sampler pays for every row with a single `3/2^p` allowance. -/
theorem named_sum_error (p A B neg a b sign D H J M K N : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K * A)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData A B neg a b sign D N))
      (qmul (step A B neg a b sign D) (reciprocalSum A B D neg (succ N)))
      (errorNumerator p D H K) (errorDenominator p D) := by
  let k := exponent (succ N) p
  let x := rowData A B neg a b sign D
  have hD := h.andE₁.andE₁.andE₂
  have hd := positive_product _ _ hD hD
  have hk := positive_product _ _ hd (unit_positive k)
  have hp := positive_product _ _ hd (unit_positive p)
  have comparison : Γ ⊢[PRAAx]
      le (rawNumerator (num 4 * H * H) (num 3) (unit k) D K N * errorDenominator p D)
        (errorNumerator p D H K * rawDenominator (unit k) D) := by
    unfold GaussianLogGammaEulerTaylorMajorant.errorNumerator GaussianLogGammaEulerTaylorMajorant.errorDenominator
      errorNumerator errorDenominator coefficient
    ipra_le 3 * 𝔞 (D * D) * 𝔞 (D * D) * sl (query_budget (Γ := Γ) (succ N) p)
  have exactSample := GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) rowF rowBody p (succ N) x
  exact distance_congr exactSample.eqSymm (sum_value A B neg a b sign D N) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hk hp comparison (raw_sum_error k A B neg a b sign D H J M K N h hK))

theorem actual_Euler_logarithm_named_row_sum_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (input (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        le (var 7) (var 11 * var 1) ⟶
        distanceBounded (ap2 sumF (var 0) (sumData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 12)))
          (qmul (step (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
            (reciprocalSum (var 1) (var 2) (var 7) (var 3) (succ (var 12))))
          (errorNumerator (var 0) (var 7) (var 8) (var 11)) (errorDenominator (var 0) (var 7))) :=
  closeUniv 13 (.impI (.impI (named_sum_error _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorRows
