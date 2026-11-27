import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.ReciprocalSlopes.GaussianLogGammaEulerReciprocalSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerRepresentation
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaSeriesTerms
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# Literal complex digamma partial fractions

The finite correction is the sum of the exact rows
`1/(j+1) − 1/(z+j+1)` through `j=N−1`, with the separate term `−1/z`.
It equals `H_N − Σ_{0≤k≤N} 1/(z+k)` as an exact normalized rational
code. Adding the original `−γ` name yields a regular partial-fraction
name for each finite cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 440000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractions

open_ipra
open ComplexLogarithmRemainder (scale oneCode zeroCode)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular harmonicPoint subst_harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaHarmonicIncrement (harmonic_point_increment)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint reciprocalSum)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameReciprocal (reciprocal_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qadd ofGaussian_canonical)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_zero im_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "sum" => GaussianRationalFiniteSum.sum
local notation "reciprocalBody" => GaussianLogGammaEulerReciprocalSlope.rowBody

private def harmonicBody : PTm 2 := fraction one (succ (var 0))

def termBody : PTm 2 := differenceBody harmonicBody (shiftBody reciprocalBody)

def partialSum (z N : PTm n) : PTm n := sum termBody N (pairT zero z)

def correction (A B D neg N : PTm n) : PTm n :=
  qsub (partialSum (argument A B D neg) N) (reciprocal (argument A B D neg))

def nameF : PR 2 := addF negativeGammaF constantF

def data (A B D neg N : PTm n) : PTm n := addData negativeGammaData (correction A B D neg N)

ipra_subst partialSum

ipra_subst correction

ipra_subst data

private theorem harmonic_at (i x : PTm n) :
    Γ ⊢[PRAAx] inst2 harmonicBody i x ≐ fraction one (succ i) := by
  simpa [harmonicBody, inst2, one] using
    (Prf.eqRefl (fraction one (succ i)) : Γ ⊢[PRAAx] _)

theorem term_at (i z : PTm n) : Γ ⊢[PRAAx] inst2 termBody i (pairT zero z) ≐
    qsub (fraction one (succ i)) (reciprocal (shiftedPoint z (succ i))) := by
  have read : Γ ⊢[PRAAx] inst2 (shiftBody reciprocalBody) i z ≐ reciprocal (shiftedPoint z (succ i)) := by
    rw [inst2_shiftBody]
    exact GaussianLogGammaEulerReciprocalSlope.row_at z (succ i)
  exact (difference_body_at harmonicBody (shiftBody reciprocalBody) i zero z).eqTrans
    (qsub_congr (harmonic_at i zero) read)

private def harmonicLaw (N : PTm n) : Fm PTm n := sum harmonicBody N zero ≐ harmonicPoint N

@[simp] private theorem subst_harmonicLaw {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    (harmonicLaw N).subst σ = harmonicLaw (Syn.subst σ N) := by simp [harmonicLaw]

private theorem harmonic_step (N : PTm n) (h : Γ ⊢[PRAAx] harmonicLaw N) :
    Γ ⊢[PRAAx] harmonicLaw (succ N) :=
  (GaussianRationalFiniteSum.sum_succ harmonicBody N zero).eqTrans
    ((qadd_congr h ((harmonic_at N zero).eqTrans
      (GaussianGammaDigammaStep.unit_step_value (succ N) (zero_lt_succ N)))).eqTrans
      (harmonic_point_increment N).eqSymm)

private theorem harmonic_sum (N : PTm n) : Γ ⊢[PRAAx] harmonicLaw N := by
  have all : Γ ⊢[PRAAx] .all (harmonicLaw (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_harmonicLaw, Syn.subst_var, Syn.inst_zero]
      exact (GaussianRationalFiniteSum.sum_zero harmonicBody zero).eqTrans GaussianGammaEulerHeadQuadratic.harmonic_zero.eqSymm
    · simp only [subst_harmonicLaw, Syn.subst_var, Syn.repl_zero]
      exact harmonic_step (var 0) Prf.hyp0
  simpa only [subst_harmonicLaw, Syn.subst_var, Syn.inst_zero] using all.allE N

private theorem zero_reciprocal_row (A B D neg : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] inst2 reciprocalBody zero (argument A B D neg) ≐ reciprocal (argument A B D neg) := by
  let z := argument A B D neg
  have e : Γ ⊢[PRAAx] equal (scale zero oneCode) (zeroCode : PTm n) := by
    apply equal_of_values
    · rw [re_scale, re_zero]; ipra_simps; ring
    · rw [im_scale, im_zero]; ipra_simps; ring
  have eq : Γ ⊢[PRAAx] fraction zero one ≐ qzero :=
    GaussianGammaFiniteValueProperness.fraction_equal _ _ one (le_refl one) e
  have shifted : Γ ⊢[PRAAx] shiftedPoint z zero ≐ z :=
    (qadd_congr eq (.eqRefl z)).eqTrans (qzero_add z (ofGaussian_canonical (native A B neg) D hD))
  exact (GaussianLogGammaEulerReciprocalSlope.row_at z zero).eqTrans (reciprocal_congr shifted)

theorem partial_sum_value (z N : PTm n) : Γ ⊢[PRAAx] partialSum z N ≐
    qsub (harmonicPoint N) (sum (shiftBody reciprocalBody) N z) :=
  (finite_sum_difference harmonicBody (shiftBody reciprocalBody) N zero z).eqTrans
    (qsub_congr (harmonic_sum N) (.eqRefl _))

/-- The separate pole term and positive-index rows recover the exact finite Euler correction. -/
theorem correction_value (A B D neg N : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] correction A B D neg N ≐
      qsub (harmonicPoint N) (reciprocalSum A B D neg (succ N)) := by
  let z := argument A B D neg
  let t := sum (shiftBody reciprocalBody) N z
  let v := reciprocal z
  have split : Γ ⊢[PRAAx] reciprocalSum A B D neg (succ N) ≐ qadd v t :=
    (GaussianRationalFiniteSum.sum_shift_first reciprocalBody N z).eqTrans
      (qadd_congr (zero_reciprocal_row A B D neg hD) (.eqRefl t))
  exact (qsub_congr (partial_sum_value z N) (.eqRefl v)).eqTrans
    ((GaussianRationalInverseQuadraticAlgebra.subtract_sum (harmonicPoint N) t v).eqTrans
      (qsub_congr (.eqRefl _) ((qadd_commutative t v).eqTrans split.eqSymm)))

theorem name_regular (A B D neg N : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data A B D neg N) :=
  add_fast negativeGammaF constantF negativeGammaData (correction A B D neg N)
    negativeGamma_regular (constant_regular _)

theorem actual_complex_digamma_partial_fraction_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 2) ⟶ (correction (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        qsub (harmonicPoint (var 4)) (reciprocalSum (var 0) (var 1) (var 2) (var 3) (succ (var 4))))) :=
  closeUniv 5 (.impI (correction_value _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractions
