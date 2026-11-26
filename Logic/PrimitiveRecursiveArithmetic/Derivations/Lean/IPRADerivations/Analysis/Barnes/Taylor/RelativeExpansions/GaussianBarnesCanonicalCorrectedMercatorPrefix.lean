import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercatorCoefficients
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalCorrectedMercatorInterval
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherMercatorTranspose
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeTail
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeTail

/-!
# Exact coefficient prefix of the original finite Barnes logarithm increment

Collect the first and second derivative rows over the same retained
interval, then transpose the original higher-degree rectangle.
The left endpoint is the polynomial used by the checked Mercator
approximation to the original finite named logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCorrectedMercatorInterval (input polynomialBody polynomialData polynomial_body_at)
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm)
open GaussianBarnesCanonicalDerivativeInterval (incrementF incrementData)
open GaussianBarnesCanonicalHigherMercatorSum (data)
open GaussianBarnesCanonicalHigherMercatorTranspose (matrix)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalQuadraticBinding (secondTerm)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (rowSumBody row_sum_at)
open GaussianRationalHorner (ofGaussian qadd qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "FD" => GaussianBarnesCanonicalDerivativeTail.data
local notation "FV" => GaussianBarnesCanonicalDerivativeTail.value
local notation "FB" => GaussianBarnesCanonicalDerivativeTail.body
local notation "SD" => GaussianBarnesCanonicalSecondDerivativeTail.data
local notation "SV" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "SB" => GaussianBarnesCanonicalSecondDerivativeTail.body
local notation "T" => GaussianBarnesCanonicalHigherMercatorTranspose.polynomial
local notation "V" => GaussianBarnesCanonicalCorrectedMercatorInterval.value
local notation "gaussAdd" => GaussianRationalFiniteSum.addBody

def polynomial (z h B N r M : PTm n) : PTm n :=
  qadd (qadd (qmul (ofGaussian h B) (FV z B N r))
    (qmul (qmul (radiusPoint one two) (SV z B N r)) (power (ofGaussian h B) two)))
      (T z h B N r M)

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (z h B N r M : PTm n) :
    Syn.subst σ (polynomial z h B N r M) =
      polynomial (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ M) :=
  by simp [polynomial,one,two]

private def componentBody (t : PTm 4) : PTm 2 :=
  let x := sndT (var 1)
  Syn.subst ![fstT (fstT x),sndT (fstT x),fstT (sndT x),succ (sndT (sndT x)+var 0)] t

private def linearBody : PTm 2 := componentBody (linearTerm (var 0) (var 1) (var 2) (var 3))
private def quadraticBody : PTm 2 := componentBody (secondTerm (var 0) (var 1) (var 2) (var 3))

private theorem component_at (t : PTm 4) (z h B N M i : PTm n) : Γ ⊢[PRAAx]
    inst2 (componentBody t) i (pairT M (data z h B N)) ≐ Syn.subst ![z,h,B,succ (N+i)] t := by
  let x := pairT M (data z h B N)
  have e : Γ ⊢[PRAAx] sndT x ≐ data z h B N := snd_pair _ _
  have u : Γ ⊢[PRAAx] fstT (sndT x) ≐ pairT z h := (congrFst e).eqTrans (fst_pair _ _)
  have v : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT B N := (congrSnd e).eqTrans (snd_pair _ _)
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![fstT (fstT (sndT x)),sndT (fstT (sndT x)),fstT (sndT (sndT x)),succ (sndT (sndT (sndT x))+i)])
    (σ' := ![z,h,B,succ (N+i)]) (fun j => by
      fin_cases j
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact (congrFst v).eqTrans (fst_pair _ _)
      · exact congrSucc (congrAdd ((congrSnd v).eqTrans (snd_pair _ _)) (.eqRefl _)))
  rw [show inst2 (componentBody t) i x =
      Syn.subst ![fstT (fstT (sndT x)),sndT (fstT (sndT x)),fstT (sndT (sndT x)),succ (sndT (sndT (sndT x))+i)] t by
    simp only [componentBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp]
  exact fields

private theorem linear_at (z h B N M i : PTm n) : Γ ⊢[PRAAx]
    inst2 linearBody i (pairT M (data z h B N)) ≐ linearTerm z h B (succ (N+i)) := by
  simpa [linearBody] using component_at (Γ := Γ) (linearTerm (var 0) (var 1) (var 2) (var 3)) z h B N M i

private theorem quadratic_at (z h B N M i : PTm n) : Γ ⊢[PRAAx]
    inst2 quadraticBody i (pairT M (data z h B N)) ≐ secondTerm z h B (succ (N+i)) := by
  simpa [quadraticBody] using component_at (Γ := Γ) (secondTerm (var 0) (var 1) (var 2) (var 3)) z h B N M i

private theorem linear_sum (z h B N r M : PTm n) : Γ ⊢[PRAAx]
    sum linearBody r (pairT M (data z h B N)) ≐ qmul (ofGaussian h B) (FV z B N r) := by
  let a := ofGaussian h B
  have H : Γ ⊢[PRAAx] sum linearBody r (pairT M (data z h B N)) ≐
      sum (multiplyBody FB) r (pairT a (FD z B N)) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded linearBody (multiplyBody FB)
      r (pairT M (data z h B N)) (pairT a (FD z B N)) (.allI (.impI ?_))
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    have eq := (multiply_body_at (Γ := Δ) FB (ofGaussian (s h) (s B)) (var 0) (FD (s z) (s B) (s N))).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalDerivativeTail.body_at (s z) (s B) (s N) (var 0)))
    simpa only [s,Δ,a,Syn.shift,subst_pairT,GaussianBarnesCanonicalHigherMercatorSum.subst_data,
      GaussianBarnesCanonicalDerivativeTail.subst_data,GaussianRationalHorner.subst_ofGaussian] using
        (linear_at (Γ := Δ) (s z) (s h) (s B) (s N) (s M) (var 0)).eqTrans eq.eqSymm
  exact H.eqTrans (sum_multiply FB a r (FD z B N))

private def quadraticWeight (h B : PTm n) : PTm n :=
  qmul (power (ofGaussian h B) two) (radiusPoint one two)

private theorem reorder_quad (u h B : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul (radiusPoint one two) u) (power (ofGaussian h B) two) ≐ qmul (quadraticWeight h B) u :=
  (qmul_commutative _ _).eqTrans (qmul_associative _ _ _).eqSymm

private theorem quadratic_sum (z h B N r M : PTm n) : Γ ⊢[PRAAx]
    sum quadraticBody r (pairT M (data z h B N)) ≐
      qmul (qmul (radiusPoint one two) (SV z B N r)) (power (ofGaussian h B) two) := by
  let w := quadraticWeight h B
  have H : Γ ⊢[PRAAx] sum quadraticBody r (pairT M (data z h B N)) ≐
      sum (multiplyBody SB) r (pairT w (SD z B N)) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded quadraticBody (multiplyBody SB)
      r (pairT M (data z h B N)) (pairT w (SD z B N)) (.allI (.impI ?_))
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    let row := GaussianBarnesCanonicalSecondDerivativeRow.value (s z) (s B) (succ (s N+var 0))
    have eq := (multiply_body_at (Γ := Δ) SB (quadraticWeight (s h) (s B)) (var 0) (SD (s z) (s B) (s N))).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBarnesCanonicalSecondDerivativeTail.body_at (s z) (s B) (s N) (var 0)))
    have left := (quadratic_at (Γ := Δ) (s z) (s h) (s B) (s N) (s M) (var 0)).eqTrans (reorder_quad row (s h) (s B))
    simpa only [s,Δ,w,Syn.shift,subst_pairT,GaussianBarnesCanonicalHigherMercatorSum.subst_data,
      GaussianBarnesCanonicalSecondDerivativeTail.subst_data,quadraticWeight,GaussianRationalHorner.subst_ofGaussian,
      GaussianRationalHorner.subst_qmul,GaussianRationalReciprocal.subst_power,GaussianDominantPairAlgebra.subst_radiusPoint,
      one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using left.eqTrans eq.eqSymm
  exact H.eqTrans ((sum_multiply SB w r (SD z B N)).eqTrans (reorder_quad (SV z B N r) h B).eqSymm)

private theorem relative_input (m z h R B N H i : PTm n) (hs : Γ ⊢[PRAAx] input m z h R B N H) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalRelativeStep.source z h R B (succ (N+i)) H := by
  have grow := le_trans (le_add_right (Γ := Γ) N i) (le_succ_self (N+i))
  exact .andI (GaussianBarnesCanonicalLogTail.row_source z R B N i hs.andE₁)
    (.andI (GaussianBarnesCanonicalLogTail.row_source (add z h) R B N i hs.andE₂.andE₁)
      (.andI hs.andE₂.andE₂.andE₁ (le_trans hs.andE₂.andE₂.andE₂.andE₁ (le_mul_mono (le_refl _) grow))))

theorem coefficient_prefix (z h R B N H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B N H) :
    Γ ⊢[PRAAx] V (previous M) z h B N r ≐ polynomial z h B N r M := by
  let d := pairT M (data z h B N)
  let L := gaussAdd linearBody quadraticBody
  let U := rowSumBody matrix
  have rows : Γ ⊢[PRAAx] V (previous M) z h B N r ≐ sum (gaussAdd L U) r d := by
    refine GaussianRationalFiniteSum.sum_congr_bounded polynomialBody (gaussAdd L U)
      r (polynomialData (previous M) z h B N) d (.allI (.impI ?_))
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    let k := succ (s N+i)
    have hi : Δ ⊢[PRAAx] input (previous (s M)) (s z) (s h) (s R) (s B) (s N) (s H) := by
      simpa [Fm.shift,Syn.shift,s,Δ] using hs.shift.wk
    have lhs := (polynomial_body_at (Γ := Δ) (previous (s M)) (s z) (s h) (s B) (s N) i).eqTrans
      (GaussianBarnesCanonicalCorrectedMercatorCoefficients.coefficient_split (s z) (s h) (s R) (s B) k (s H) (s M)
        (relative_input (previous (s M)) (s z) (s h) (s R) (s B) (s N) (s H) i hi))
    have hr := (row_sum_at (Γ := Δ) matrix i (s M) (data (s z) (s h) (s B) (s N))).eqTrans
      (GaussianBarnesCanonicalHigherMercatorTranspose.row_value (s z) (s h) (s B) (s N) i (s M))
    have rhs := qadd_congr
      (qadd_congr (linear_at (Γ := Δ) (s z) (s h) (s B) (s N) (s M) i)
        (quadratic_at (s z) (s h) (s B) (s N) (s M) i)) hr
    simpa only [s,Δ,i,k,d,L,U,Syn.shift,subst_pairT,GaussianRationalFiniteSum.inst2_addBody,GaussianBarnesCanonicalHigherMercatorSum.subst_data,
      GaussianBarnesCanonicalCorrectedMercatorInterval.subst_polynomialData,GaussianBarnesCanonicalHigherRows.subst_previous] using
        lhs.eqTrans rhs.eqSymm
  exact rows.eqTrans ((GaussianRationalFiniteSum.sum_add L U r d).eqTrans
    (qadd_congr ((GaussianRationalFiniteSum.sum_add linearBody quadraticBody r d).eqTrans
      (qadd_congr (linear_sum z h B N r M) (quadratic_sum z h B N r M)))
      (GaussianBarnesCanonicalHigherMercatorTranspose.transpose z h B N r M)))

theorem coefficient_rate (z h R B N H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B N H) :
    Γ ⊢[PRAAx] independentRate incrementF constantF (incrementData z h R B N r) (polynomial z h B N r M)
      (GaussianBarnesCanonicalCorrectedMercator.numerator (previous M) H*r)
      (GaussianBarnesCanonicalCorrectedMercatorInterval.errorDenominator (previous M) B N r) := by
  let X := incrementData z h R B N r
  let Y := V (previous M) z h B N r
  let P := polynomial z h B N r M
  let A := GaussianBarnesCanonicalCorrectedMercator.numerator (previous M) H*r
  let D := GaussianBarnesCanonicalCorrectedMercatorInterval.errorDenominator (previous M) B N r
  have e : Γ ⊢[PRAAx] Y ≐ P := coefficient_prefix z h R B N H r M hs
  have r := GaussianBarnesCanonicalCorrectedMercatorInterval.rate (previous M) z h R B N H r hs
  simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Matrix.cons_val] using
    Prf.eqSubst (independentRate incrementF constantF (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
      ![X,Y,A,D] ![X,P,A,D] (fun j => by fin_cases j; exact .eqRefl _; exact e; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Matrix.cons_val] using r)

theorem actual_Barnes_corrected_Mercator_coefficient_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let N := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     input (previous M) z h R B N H ⟶ (V (previous M) z h B N r ≐ polynomial z h B N r M)) :=
  closeUniv 8 (.impI (coefficient_prefix _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectedMercatorPrefix
