import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleySquareGap
import IPRADerivations.Analysis.Trigonometry.GaussianSineSquaredTrace
import IPRADerivations.Analysis.Names.GaussianNameReciprocal

/-!
# Separation for complements of sampled squared sines

A positive real gap between squared Cayley sines gives a lower
Euclidean bound on the difference of the corresponding trace roots.
The affine change from squared sine to trace is verified at the
actual Gaussian rational codes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSquaredRootSeparation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode normSq normSq_eval re im eval_re_code eval_im_code)
open GaussianArctangentCayleySquareGap (sqNumerator sqDenominator squareValue square_represents)
open GaussianArctangentCayleyTrig (sineCode sinePoint)
open GaussianArctangentCayleyValues (denominator denominator_positive)
open GaussianNameReciprocal (lower)
open GaussianRationalHorner (qmul represents represents_congr represents_rescale qmul_represents ofGaussian_represents
  scalar_congr positive_product)
open GaussianRationalMetric (qsub qsub_represents qnormSq_represents squared_tolerance_represents
  comparison_to_cleared comparison_of_cleared)
open GaussianRationalNaturalScale (natScale_as_product natScale_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (sub equal_of_values equal_refl re_mul im_mul re_scale im_scale re_one im_one re_sub im_sub)
open GaussianSineSquaredTrace (fromSine)
open RationalArithmetic (add)
open RationalArgmin (rationalLE)
open RationalCubeMidpoint (fraction fraction_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem sqDen_positive (M i : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (sqDenominator M i) :=
  positive_product _ _ (denominator_positive M i hM) (denominator_positive M i hM)

private theorem square_gaussian_represents (M i : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] represents (qmul (sinePoint M i) (sinePoint M i)) (scale (sqNumerator M i) oneCode) (sqDenominator M i) := by
  let a := sineCode M i
  let D := denominator M i
  have hd := denominator_positive M i hM
  have v := ofGaussian_represents (Γ := Γ) a D hd
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (qmul_represents _ _ _ _ _ _ hd hd v v)
  apply equal_of_values <;>
    simp only [a,sineCode,sqNumerator,re_mul,im_mul,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

def traceCode (M i : PTm n) : PTm n :=
  scale (num 4) (sub (scale (sqDenominator M i) oneCode) (scale (sqNumerator M i) oneCode))

private theorem trace_represents (M i : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] represents (fromSine (sinePoint M i)) (traceCode M i) (sqDenominator M i) := by
  have h := qsub_represents qone _ _ _ _ (sqDen_positive M i hM) (qone_represents_scaled _)
    (square_gaussian_represents M i hM)
  exact represents_congr (natScale_as_product _ _) (equal_refl _) (.eqRefl _)
    (natScale_represents (num 4) _ _ _ (sqDen_positive M i hM) h)

private theorem gap_cleared (M i N j S : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le one S)
    (gap : Γ ⊢[PRAAx] rationalLE (add (squareValue M i) (fraction one S)) (squareValue N j)) :
    Γ ⊢[PRAAx] le (sqDenominator M i*sqDenominator N j)
      (S*monus (sqNumerator N j*sqDenominator M i) (sqNumerator M i*sqDenominator N j)) := by
  let E := sqDenominator M i
  let F := sqDenominator N j
  let a := sqNumerator M i
  let b := sqNumerator N j
  let G := monus (b*E) (a*F)
  have lhs : Γ ⊢[PRAAx] RationalArithmetic.represents (add (squareValue M i) (fraction one S))
      (ZT.ofNat (a*S+E)) (E*S) := by
    apply scalar_congr (.eqRefl _) _ (.eqRefl _)
      (RationalRepresentations.represents_add _ _ _ _ _ _ (square_represents M i hM) (fraction_represents one S hS))
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
    ring
  have cleared : Γ ⊢[PRAAx] le (E*F+S*(a*F)) (S*(b*E)) :=
    le_congr (by ipra_ring) (by ipra_ring) (comparison_to_cleared _ _ _ _ _ _ lhs (square_represents N j hN) gap)
  have order : Γ ⊢[PRAAx] le (a*F) (b*E) := RationalValueBounds.positive_cancel hS
    (le_trans (le_add_left _ _) cleared)
  have right : Γ ⊢[PRAAx] S*(b*E) ≐ S*G+S*(a*F) :=
    (congrMul (.eqRefl _) (eq_add_of_le order)).eqTrans (by dsimp only [G]; ipra_ring)
  exact le_of_add_le_add_right (le_congr (.eqRefl _) right cleared)

private theorem trace_difference_norm (M i N j : PTm n)
    (h : Γ ⊢[PRAAx] le (sqNumerator M i*sqDenominator N j) (sqNumerator N j*sqDenominator M i)) :
    Γ ⊢[PRAAx] normSq (sub (scale (sqDenominator M i) (traceCode N j)) (scale (sqDenominator N j) (traceCode M i))) ≐
      (num 4*monus (sqNumerator N j*sqDenominator M i) (sqNumerator M i*sqDenominator N j))*
      (num 4*monus (sqNumerator N j*sqDenominator M i) (sqNumerator M i*sqDenominator N j)) := by
  let g := monus (sqNumerator N j*sqDenominator M i) (sqNumerator M i*sqDenominator N j)
  let d := sub (scale (sqDenominator M i) (traceCode N j)) (scale (sqDenominator N j) (traceCode M i))
  have gap := natEq (eq_add_of_le h)
  have reEq : ZT.toZ Γ (re d) = -4*𝔞 g := by
    simp only [d,traceCode,re_sub,re_scale,re_one]
    dsimp only [g]
    ipra_simps
    linear_combination -4*gap
  have imEq : ZT.toZ Γ (im d) = 0 := by
    simp only [d,traceCode,im_sub,im_scale,im_one]
    ring
  apply deriveNat
  change 𝔞 (normSq d) = 𝔞 ((num 4*g)*(num 4*g))
  rw [normSq_eval,reEq,imEq]
  ipra_simps
  ring

theorem root_gap (M i N j S : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le one S)
    (gap : Γ ⊢[PRAAx] rationalLE (add (squareValue M i) (fraction one S)) (squareValue N j)) :
    Γ ⊢[PRAAx] lower (qsub (fromSine (sinePoint N j)) (fromSine (sinePoint M i))) S := by
  let E := sqDenominator M i
  let F := sqDenominator N j
  let a := sqNumerator M i
  let b := sqNumerator N j
  let G := monus (b*E) (a*F)
  let d := sub (scale E (traceCode N j)) (scale F (traceCode M i))
  let v := qsub (fromSine (sinePoint N j)) (fromSine (sinePoint M i))
  have ep := sqDen_positive M i hM
  have fp := sqDen_positive N j hN
  have p := positive_product _ _ ep fp
  have raw := gap_cleared M i N j S hM hN hS gap
  have hp : Γ ⊢[PRAAx] le one G := GaussianDominantScalarOrder.factor_positive_left G S
    (le_congr (.eqRefl _) (mul_comm _ _) (le_trans p raw))
  have order : Γ ⊢[PRAAx] le (a*F) (b*E) := by
    refine .orE (lt_or_le (b*E) (a*F)) ?_ Prf.hyp0
    have e : (lt (b*E) (a*F) :: Γ) ⊢[PRAAx] G ≐ ConciseIPRA.PTm.zero := le_of_lt Prf.hyp0
    exact .botE _ (lt_irrefl _ _ (lt_congr (.eqRefl _) e hp.wk))
  have rep : Γ ⊢[PRAAx] represents v d (E*F) :=
    qsub_represents _ _ _ _ _ p
      (rescale_to _ _ _ _ _ (trace_represents N j hN) (mul_comm _ _))
      (represents_rescale _ _ _ _ (trace_represents M i hM))
  have hsquare := qnormSq_represents v d (E*F) p rep
  have size := trace_difference_norm M i N j order
  have raw' : Γ ⊢[PRAAx] le (E*F) (S*(num 4*G)) :=
    le_trans raw (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (S*G) (num 3*S*G)))
  exact comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hS hS) (positive_product _ _ p p)
    (squared_tolerance_represents one S hS) hsquare
    (le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] (S*(num 4*G))*(S*(num 4*G)) ≐
      ((num 4*G)*(num 4*G))*(S*S)).eqTrans (congrMul size.eqSymm (.eqRefl _))) (le_mul_mono raw' raw'))

theorem actual_squared_sine_root_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (((le one (var 0) ⋏ le one (var 2)) ⋏ le one (var 4)) ⟶
      rationalLE (add (squareValue (var 0) (var 1)) (fraction one (var 4))) (squareValue (var 2) (var 3)) ⟶
      lower (qsub (fromSine (sinePoint (var 2) (var 3))) (fromSine (sinePoint (var 0) (var 1)))) (var 4)) :=
  closeUniv 5 (.impI (.impI (root_gap _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineSquaredRootSeparation
