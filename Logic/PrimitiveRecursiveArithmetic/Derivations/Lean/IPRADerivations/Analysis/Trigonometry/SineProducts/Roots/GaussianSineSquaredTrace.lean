import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSquaredPolynomial
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineFromExponential
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.RootProducts.GaussianRationalFiniteRoots

/-!
# The squared trace in the sine polynomial

The trace A+B for inverse Gaussian points has square 4(1−s²), where
s is the same scaled difference used by the named sine constructor.
An odd-power equality therefore gives a zero of the monic trace
polynomial at 4(1−s²) when the sine is nonzero.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSquaredTrace

open_ipra
open ComplexLogarithmRemainder (scale mul add eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianNamedSineFromExponential (multiplier)
open GaussianRationalHorner (qzero qadd qmul evaluate canonical canonical_unique canonical_congr
  qadd_canonical qmul_canonical qadd_represents qmul_represents represents represents_congr represents_rescale
  ofGaussian_represents positive_product)
open GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open GaussianRationalNaturalScale (naturalPoint natScale_represents natScale_as_product)
open GaussianRationalReciprocal (qone power)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr qmul_zero_right)
open GaussianRationalValueEquality (commonDen common_den_positive leftValue rightValue
  common_left_represents common_right_represents)
open GaussianRootAlgebra (equal equal_refl equal_of_values re_scale im_scale re_add im_add re_sub im_sub
  re_mul im_mul re_neg im_neg)
open GaussianSineSquaredPolynomial (coefficients evaluation_square)
open GaussianSineMultipleAngleRecurrence (evenValue power_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sineValue (A B : PTm n) : PTm n := qmul multiplier (qsub A B)
def fromSine (s : PTm n) : PTm n := qmul (naturalPoint (num 4)) (qsub qone (qmul s s))

theorem squared_trace (A B : PTm n) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (qadd A B) (qadd A B) ≐ fromSine (sineValue A B) := by
  let E := commonDen A B
  let W := (two*E)*(two*E)
  let a := leftValue A B
  let b := rightValue A B
  let d := GaussianRootAlgebra.sub a b
  let m := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  let s := mul m d
  let t := add a b
  let v := GaussianRootAlgebra.sub (scale (num 4) (mul a b)) (mul s s)
  let sActual := sineValue A B
  let cActual := qsub qone (qmul sActual sActual)
  have hE := common_den_positive (Γ := Γ) A B
  have hTwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hD := positive_product two E hTwo hE
  have hW := positive_product _ _ hD hD
  have ra := common_left_represents (Γ := Γ) A B
  have rb := common_right_represents (Γ := Γ) A B
  have inv := represents_congr hAB (equal_refl _) (.eqRefl _)
    (qmul_represents A B a b E E hE hE ra rb)
  have oneRep : Γ ⊢[PRAAx] represents qone (scale (num 4) (mul a b)) W :=
    represents_congr (.eqRefl _) (equal_refl _) (by dsimp only [W]; ipra_ring)
      (represents_rescale _ _ _ (num 4) inv)
  have rs : Γ ⊢[PRAAx] represents sActual s (two*E) :=
    qmul_represents multiplier (qsub A B) m d two E hTwo hE (ofGaussian_represents _ _ hTwo)
      (qsub_represents _ _ _ _ _ hE ra rb)
  have rSub : Γ ⊢[PRAAx] represents cActual v W :=
    qsub_represents _ _ _ _ _ hW oneRep (qmul_represents _ _ s s _ _ hD hD rs rs)
  have rRhs : Γ ⊢[PRAAx] represents (fromSine sActual) (scale (num 4) v) W :=
    represents_congr (natScale_as_product _ _) (equal_refl _) (.eqRefl _)
      (natScale_represents _ _ _ _ hW rSub)
  have rTrace : Γ ⊢[PRAAx] represents (qadd A B) t E := qadd_represents _ _ _ _ _ hE ra rb
  have rLhs := represents_rescale _ _ _ (num 4)
    (qmul_represents _ _ t t E E hE hE rTrace rTrace)
  have eq : Γ ⊢[PRAAx] equal (scale (num 4) (mul t t)) (scale (num 4) v) := by
    apply equal_of_values <;>
      simp only [v,s,d,m,t,imaginaryCode,re_scale,im_scale,re_mul,im_mul,re_add,im_add,re_sub,im_sub,
        re_neg,im_neg,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ W (qmul_canonical _ _) (qmul_canonical _ _) hW
    (represents_congr (.eqRefl _) eq (by dsimp only [W]; ipra_ring) rLhs) rRhs

theorem evaluation_at_sine (A B J : PTm n) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] evaluate (coefficients J) (fromSine (sineValue A B)) ≐ evenValue (qadd A B) J :=
  (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (squared_trace A B hAB).eqSymm).eqTrans
    (evaluation_square _ J (qadd_canonical _ _))

theorem root_of_power_equal (A B J : PTm n) (hA : Γ ⊢[PRAAx] canonical A) (hB : Γ ⊢[PRAAx] canonical B)
    (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone)
    (hsin : Γ ⊢[PRAAx] neg (sineValue A B ≐ qzero))
    (hpower : Γ ⊢[PRAAx] power A (succ (two*J)) ≐ power B (succ (two*J))) :
    Γ ⊢[PRAAx] evaluate (coefficients J) (fromSine (sineValue A B)) ≐ qzero := by
  let d := qsub A B
  let v := evenValue (qadd A B) J
  have nonzero : Γ ⊢[PRAAx] neg (d ≐ qzero) := by
    refine .impI (.impE hsin.wk ?_)
    exact (qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (qmul_zero_right _)
  have read := evaluation_at_sine A B J hAB
  have hv : Γ ⊢[PRAAx] canonical v :=
    canonical_congr read.eqSymm (GaussianRationalHorner.horner_canonical _ _ _)
  have zeroProduct : Γ ⊢[PRAAx] qmul d v ≐ qzero :=
    (power_difference A B (two*J) hA hB hAB).eqTrans
      ((qsub_congr hpower (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _))
  exact read.eqTrans (GaussianRationalFiniteRoots.product_zero_reflect d v
    (qsub_canonical _ _) hv nonzero zeroProduct)

theorem actual_sine_squared_trace_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((qmul (var 0) (var 1) ≐ qone) ⟶ qmul (qadd (var 0) (var 1)) (qadd (var 0) (var 1)) ≐
      fromSine (sineValue (var 0) (var 1))) :=
  closeUniv 2 (.impI (squared_trace _ _ Prf.hyp0))

theorem actual_sine_polynomial_root_of_odd_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((canonical (var 0) ⋏ canonical (var 1)) ⟶ (qmul (var 0) (var 1) ≐ qone) ⟶
      neg (sineValue (var 0) (var 1) ≐ qzero) ⟶
      (power (var 0) (succ (two*var 2)) ≐ power (var 1) (succ (two*var 2))) ⟶
        evaluate (coefficients (var 2)) (fromSine (sineValue (var 0) (var 1))) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (root_of_power_equal _ _ _ hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianSineSquaredTrace
