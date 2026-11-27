import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorBuffer
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Exact evaluation of the stored Barnes exponent polynomial

The first three slots in ascending power order give the zero, linear
and quadratic terms. The rest are exactly the checked transposed
higher coefficient sum. Evaluation uses the original Horner program.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBufferEvaluation

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer buffer_length coefficient entry_at coefficient_zero coefficient_one coefficient_two coefficient_high
    linearCoefficient quadraticCoefficient highCoefficient subst_buffer)
open GaussianBarnesCanonicalHigherRows (degree previous)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalHigherMercatorSum (data subst_data)
open GaussianBarnesCanonicalHigherMercatorTranspose (degreeValue degreeBody polynomial degree_at)
open GaussianRationalHorner (ofGaussian evaluate qadd qmul qzero qmul_canonical ofGaussian_canonical)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_add qmul_zero_left)
open GaussianRationalFiniteSum (sum sum_succ sum_zero sum_index_congr sum_congr_bounded)
open GaussianRationalPowerExpansion (termBody term_body_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "powerData" => GaussianRationalPowerExpansion.data
local notation "off" => offB
local notation "Nₘ" => GaussianBarnesCanonicalHigherRows.previous

def expanded (q z h R B r M : PTm n) : PTm n :=
  let d := ofGaussian h B
  qadd (qadd (qmul (linearCoefficient q z R B r) d) (qmul (quadraticCoefficient q z R B r) (power d two)))
    (polynomial z h B (initial R) r M)

private theorem power_term (q z R B r M d e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] inst2 termBody e (powerData (buffer q z R B r M) (previous M) d) ≐
      qmul (coefficient q z R B r e) (power d e) :=
  (term_body_at _ _ _ _).eqTrans (qmul_congr (entry_at q z R B r M e he) (.eqRefl _))

private theorem low_sum (q z h R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    let d := ofGaussian h B
    let x := powerData (buffer q z R B r M) (previous M) d
    Γ ⊢[PRAAx] sum termBody (num 3) x ≐
      qadd (qmul (linearCoefficient q z R B r) d) (qmul (quadraticCoefficient q z R B r) (power d two)) := by
  let d := ofGaussian h B
  let x := powerData (buffer q z R B r M) (previous M) d
  have hm : Γ ⊢[PRAAx] le two (previous M) :=
    LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ M)
  have hOne := le_trans (le_succ_self one) hm
  have e0 := (power_term (Γ := Γ) q z R B r M d zero (zero_le _)).eqTrans
    ((qmul_congr (coefficient_zero q z R B r) (.eqRefl _)).eqTrans (qmul_zero_left _))
  have e1 := (power_term q z R B r M d one hOne).eqTrans
    (qmul_congr (coefficient_one q z R B r) (GaussianRationalPowerAlgebra.power_one d (ofGaussian_canonical _ _ hB)))
  have e2 := (power_term q z R B r M d two hm).eqTrans (qmul_congr (coefficient_two q z R B r) (.eqRefl _))
  have z0 : Γ ⊢[PRAAx] sum termBody one x ≐ qzero :=
    GaussianRationalFiniteSum.sum_singleton termBody x e0
      GaussianRationalSyntheticDivision.qzero_canonical
  have z1 : Γ ⊢[PRAAx] sum termBody two x ≐ qmul (linearCoefficient q z R B r) d :=
    (GaussianRationalFiniteSum.sum_succ termBody one x).eqTrans
      ((qadd_congr z0 e1).eqTrans (qzero_add (qmul (linearCoefficient q z R B r) d) (qmul_canonical _ _)))
  exact (GaussianRationalFiniteSum.sum_succ termBody two x).eqTrans (qadd_congr z1 e2)

private theorem add_three (j : PTm n) : Γ ⊢[PRAAx] num 3+j ≐ degree j := by
  unfold degree previous
  ipra_ring

private theorem high_sum (q z h R B r M : PTm n) :
    let d := ofGaussian h B
    let x := powerData (buffer q z R B r M) (previous M) d
    Γ ⊢[PRAAx] sum (off termBody) M (pairT (num 3) x) ≐ polynomial z h B (initial R) r M := by
  let d := ofGaussian h B
  let x := powerData (buffer q z R B r M) (previous M) d
  let y := pairT r (data z h B (initial R))
  refine GaussianRationalFiniteSum.sum_congr_bounded (off termBody) degreeBody M (pairT (num 3) x) y (.allI (.impI ?_))
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (s M) :: Γ.map Fm.shift
  let N := previous (s M)
  let D := ofGaussian (s h) (s B)
  let X := powerData (buffer (s q) (s z) (s R) (s B) (s r) (s M)) N D
  have hN : Δ ⊢[PRAAx] le (degree j) N :=
    LeanProofs.IPRA.Common.succ_le_succ (LeanProofs.IPRA.Common.succ_le_succ Prf.hyp0)
  have eq := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) termBody (num 3) j X).eqTrans
    (by simpa only [subst_inst2,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr1 (inst2 termBody (var 0) (Syn.shift X)) (add_three (Γ := Δ) j))
  have left := eq.eqTrans ((power_term (s q) (s z) (s R) (s B) (s r) (s M) D (degree j) hN).eqTrans
    (qmul_congr (coefficient_high (s q) (s z) (s R) (s B) (s r) j) (.eqRefl _)))
  have right := degree_at (Γ := Δ) (s z) (s h) (s B) (initial (s R)) (s r) j
  simpa only [Δ,s,j,N,D,X,x,y,d,Syn.shift,subst_pairT,PTm.subst_num,GaussianRationalPowerExpansion.subst_data,
    subst_buffer,GaussianBarnesCanonicalHigherRows.subst_previous,GaussianRationalHorner.subst_ofGaussian,
    subst_data,GaussianBarnesCanonicalLogSchedule.subst_initial,degreeValue,highCoefficient] using left.eqTrans right.eqSymm

theorem evaluate_eq (q z h R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] evaluate (buffer q z R B r M) (ofGaussian h B) ≐ expanded q z h R B r M := by
  let C := buffer q z R B r M
  let N := previous M
  let d := ofGaussian h B
  let x := powerData C N d
  have e : Γ ⊢[PRAAx] succ N ≐ num 3+M := (add_three M).eqSymm
  have read := GaussianBivariatePowerExpansion.evaluate_power_sum (Γ := Γ) C N d (buffer_length q z R B r M)
  exact read.eqTrans ((sum_index_congr termBody e (.eqRefl x)).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_split termBody (num 3) M x).eqTrans
      (qadd_congr (low_sum q z h R B r M hB) (high_sum q z h R B r M))))

theorem actual_Barnes_exponent_buffer_Horner_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let q := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     le one B ⟶ evaluate (buffer q z R B r M) (ofGaussian h B) ≐ expanded q z h R B r M) :=
  closeUniv 7 (.impI (evaluate_eq _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBufferEvaluation
