import IPRADerivations.Analysis.Trigonometry.GaussianSineSquaredTrace
import IPRADerivations.Analysis.Names.GaussianNameReciprocal
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Sine polynomial residual from an odd power difference

For exact inverse Gaussian rational samples, multiplying the trace
polynomial by the sine gives the odd power difference scaled by −i/2.
A lower bound on the sampled sine therefore gives a residual estimate
on the actual monic coefficient list at the sampled squared trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSquaredResidual

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianNameReciprocal (lower lower_norm_positive inverse_bound)
open GaussianNamedSineFromExponential (multiplier)
open GaussianRationalHorner (canonical qmul evaluate ofGaussian_represents horner_canonical)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (qone power reciprocal reciprocal_identity bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianSineSquaredPolynomial (coefficients)
open GaussianSineSquaredTrace (sineValue fromSine evaluation_at_sine)
open GaussianSineMultipleAngleRecurrence (evenValue power_difference)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sampled_sine_product (A B J : PTm n) (hA : Γ ⊢[PRAAx] canonical A)
    (hB : Γ ⊢[PRAAx] canonical B) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (sineValue A B) (evaluate (coefficients J) (fromSine (sineValue A B))) ≐
      qmul multiplier (qsub (power A (succ (two*J))) (power B (succ (two*J)))) :=
  (qmul_congr (.eqRefl _) (evaluation_at_sine A B J hAB)).eqTrans
    ((qmul_associative multiplier (qsub A B) (evenValue (GaussianRationalHorner.qadd A B) J)).eqTrans
      (qmul_congr (.eqRefl _) (power_difference A B (two*J) hA hB hAB)))

theorem multiplier_bound : Γ ⊢[PRAAx] bounded (multiplier : PTm n) one two := by
  let a := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have size : Γ ⊢[PRAAx] normSq a ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [a,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,imaginaryCode,
      eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact bounded_of_cleared _ a two one two htwo htwo (ofGaussian_represents _ _ htwo)
    (le_congr (congrMul (.eqRefl _) size).eqSymm (by ipra_ring) (le_refl _))

theorem residual_bound_sharp (A B J E K D : PTm n) (hA : Γ ⊢[PRAAx] canonical A)
    (hB : Γ ⊢[PRAAx] canonical B) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone)
    (hK : Γ ⊢[PRAAx] le one K) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] lower (sineValue A B) D)
    (hPow : Γ ⊢[PRAAx] distanceBounded (power A (succ (two*J))) (power B (succ (two*J))) E K) :
    Γ ⊢[PRAAx] bounded (evaluate (coefficients J) (fromSine (sineValue A B))) (D*E) (two*K) := by
  let s := sineValue A B
  let p := evaluate (coefficients J) (fromSine s)
  let w := qsub (power A (succ (two*J))) (power B (succ (two*J)))
  let u := qmul multiplier w
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have twoK := GaussianRationalHorner.positive_product _ _ htwo hK
  have hInv : Γ ⊢[PRAAx] qmul (reciprocal s) s ≐ qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity s (lower_norm_positive s D hD hs))
  have hProduct := bounded_product multiplier w one two E K htwo hK multiplier_bound hPow
  have q : Γ ⊢[PRAAx] qmul (reciprocal s) u ≐ p :=
    (qmul_congr (.eqRefl _) (sampled_sine_product A B J hA hB hAB).eqSymm).eqTrans
      (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product _ _ _ (horner_canonical _ _ _) hInv)
  exact bound_congr q (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl _) twoK (inverse_bound s D hD hs) hProduct)

theorem residual_bound (A B J E K D : PTm n) (hA : Γ ⊢[PRAAx] canonical A)
    (hB : Γ ⊢[PRAAx] canonical B) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone)
    (hK : Γ ⊢[PRAAx] le one K) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] lower (sineValue A B) D)
    (hPow : Γ ⊢[PRAAx] distanceBounded (power A (succ (two*J))) (power B (succ (two*J))) E K) :
    Γ ⊢[PRAAx] bounded (evaluate (coefficients J) (fromSine (sineValue A B))) (D*E) K :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (le_succ_self one) hK) hK
    (le_of_eq_add (d := D*E*K) (by ipra_ring))
    (residual_bound_sharp A B J E K D hA hB hAB hK hD hs hPow)

theorem actual_sine_polynomial_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (((canonical (var 0) ⋏ canonical (var 1)) ⋏ (qmul (var 0) (var 1) ≐ qone)) ⟶
      ((le one (var 4) ⋏ le one (var 5)) ⋏ lower (sineValue (var 0) (var 1)) (var 5)) ⟶
      distanceBounded (power (var 0) (succ (two*var 2))) (power (var 1) (succ (two*var 2))) (var 3) (var 4) ⟶
      bounded (evaluate (coefficients (var 2)) (fromSine (sineValue (var 0) (var 1))))
        (var 5*var 3) (two*var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (residual_bound_sharp _ _ _ _ _ _
    hyp2.andE₁.andE₁ hyp2.andE₁.andE₂ hyp2.andE₂ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineSquaredResidual
