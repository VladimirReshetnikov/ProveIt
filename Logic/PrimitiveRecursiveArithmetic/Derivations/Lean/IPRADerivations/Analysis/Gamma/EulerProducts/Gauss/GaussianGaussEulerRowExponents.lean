import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaEulerShift

/-!
# Relative Euler exponents for Gauss multiplication

At a fixed Euler cutoff the original exponential in every shifted row
equals the reference row's exponential times the same factor
(N^{-(z/B-1/m)}). The checked identity uses the literal log sampler
and independently certified radii for the three exponential names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerRowExponents

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaEulerShift (constant_sum_cross expF)
open GaussianGammaFiniteApproximantName (logF logExponentF logExponentData log_regular log_exponent_regular
  exponential_input exponentialInputData)
open GaussianGammaGaussReference (offset negative_row_sum)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianRationalHorner (ofGaussian qadd)
open GaussianRationalMetric (qnegative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftedExponent (z B m r N : PTm n) : PTm n :=
  logExponentData (shiftedNumerator z B m r) (B*m) N
def referenceExponent (m r N : PTm n) : PTm n := logExponentData (scale (succ r) oneCode) m N
def offsetExponent (z B m N : PTm n) : PTm n := multiplyData logF constantF N (qnegative (offset z B m))
def exponentSum (z B m r N : PTm n) : PTm n := addData (referenceExponent m r N) (offsetExponent z B m N)

theorem exponent_factorization (z B m r N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (addF logExponentF logExponentF) logExponentF
      (exponentSum z B m r N) (shiftedExponent z B m r N) := by
  let a := qnegative (ofGaussian (scale (succ r) oneCode) m)
  let b := qnegative (offset z B m)
  let c := qnegative (ofGaussian (shiftedNumerator z B m r) (B*m))
  have hL := log_regular (Γ := Γ) N hN
  have ca := constant_regular (Γ := Γ) a
  have cb := constant_regular (Γ := Γ) b
  have hsum := cross_trans _ _ _ _ _ _ (constant_sum_cross a b)
    (constant_data_cross (qadd a b) c (negative_row_sum z B m r hB hm).eqSymm)
  have product := GaussianGammaAdjacentCutoff.multiply_cross logF logF (addF constantF constantF) constantF
    N N (addData a b) c hL hL (add_fast _ _ _ _ ca cb) (constant_regular c) (cross_refl _ _ hL) hsum
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNameRingLaws.distributive logF constantF constantF
    N a b hL ca cb)) product

def expData (x : PTm n) : PTm n := exponentialInputData logExponentF x

theorem exponential_factorization (z B m r N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF expF expF) expF
      (multiplyData expF expF (expData (referenceExponent m r N)) (expData (offsetExponent z B m N)))
      (expData (shiftedExponent z B m r N)) := by
  have ref := log_exponent_regular (Γ := Γ) (scale (succ r) oneCode) m N hN
  have off := multiply_fast logF constantF N (qnegative (offset z B m)) (log_regular N hN) (constant_regular _)
  have tgt := log_exponent_regular (Γ := Γ) (shiftedNumerator z B m r) (B*m) N hN
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent logExponentF logExponentF logExponentF
    _ _ _ _ _ _ (exponential_input _ _ ref) (exponential_input _ _ off) (exponential_input _ _ tgt)
    (exponent_factorization z B m r N hB hm hN)

theorem original_Gauss_row_exponential_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 4) ⟶ crossEquivalent (multiplyF expF expF) expF
      (multiplyData expF expF (expData (referenceExponent (var 2) (var 3) (var 4)))
        (expData (offsetExponent (var 0) (var 1) (var 2) (var 4))))
      (expData (shiftedExponent (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (exponential_factorization _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerRowExponents
