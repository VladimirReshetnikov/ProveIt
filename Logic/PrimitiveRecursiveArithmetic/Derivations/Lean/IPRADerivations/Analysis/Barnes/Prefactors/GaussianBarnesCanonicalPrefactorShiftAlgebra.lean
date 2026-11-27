import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.FiniteProducts.GaussianBarnesCanonicalShiftChart
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalSquareCancellation
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# Rational calculation of the Barnes prefactor exponent difference

The two original polynomial exponents differ by the Stirling constant
minus `1/2` minus the product of `1+γ` and the shifted midpoint.
This equality uses arbitrary rational observations of the two constants.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShiftAlgebra

open_ipra
open GaussianBarnesCanonicalCorrectionShift (halfShift)
open GaussianBarnesCanonicalPrefactor (negativeHalf)
open GaussianBarnesCanonicalShiftChart (translated_difference negative_half_mul_sum)
open GaussianGammaEulerHeadLower (translated)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalHorner (canonical ofGaussian qadd qadd_canonical qmul)
open GaussianRationalMetric (qnegative qsub qnegative_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalRoundedPower (multiplication_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (x g : PTm n) : PTm n := qadd x (qmul (qmul x x) g)
def exponent (x s g : PTm n) : PTm n := qadd (qmul x s) (qmul negativeHalf (polynomial x g))
def shift (z B s g : PTm n) : PTm n := qadd s (qadd negativeHalf (qmul (qnegative (halfShift z B)) g))

private theorem right_difference (t u v : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul u t) (qmul v t) ≐ qmul (qsub u v) t :=
  (qsub_congr (qmul_commutative u t) (qmul_commutative v t)).eqTrans
    ((multiplication_difference t u v).eqTrans (qmul_commutative _ _))

theorem exponent_shift (z B s g : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] canonical s) : Γ ⊢[PRAAx]
    qsub (exponent (ofGaussian (translated z B one) B) s g) (exponent (ofGaussian z B) s g) ≐ shift z B s g := by
  let x := ofGaussian z B
  let y := ofGaussian (translated z B one) B
  let h := halfShift z B
  let a : PTm n := negativeHalf
  have unitStep := translated_difference z B hB
  have square : Γ ⊢[PRAAx] qsub (qmul y y) (qmul x x) ≐ qadd y x :=
    (GaussianRationalSquareCancellation.difference_factorization y x).eqTrans
      ((qmul_congr unitStep (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right _ (qadd_canonical _ _))))
  have poly : Γ ⊢[PRAAx] qsub (polynomial y g) (polynomial x g) ≐ qadd qone (qmul (qadd y x) g) :=
    (sum_difference y x (qmul (qmul y y) g) (qmul (qmul x x) g)).eqTrans
      (qadd_congr unitStep ((right_difference g _ _).eqTrans (qmul_congr square (.eqRefl _))))
  have lin : Γ ⊢[PRAAx] qsub (qmul y s) (qmul x s) ≐ s :=
    (right_difference s y x).eqTrans ((qmul_congr unitStep (.eqRefl _)).eqTrans
      ((qmul_commutative _ _).eqTrans (qmul_one_right s hs)))
  have corr : Γ ⊢[PRAAx] qsub (qmul a (polynomial y g)) (qmul a (polynomial x g)) ≐
      qadd a (qmul (qnegative h) g) :=
    (multiplication_difference a _ _).eqTrans ((qmul_congr (.eqRefl _) poly).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
        (qadd_congr (qmul_one_right a (qnegative_canonical _))
          ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (negative_half_mul_sum z B hB) (.eqRefl _))))))
  exact (sum_difference (qmul y s) (qmul x s) (qmul a (polynomial y g)) (qmul a (polynomial x g))).eqTrans
    (qadd_congr lin corr)

theorem actual_Barnes_prefactor_exponent_shift_algebra_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let B := var 1
     let s := var 2
     let g := var 3
     le one B ⟶ canonical s ⟶ qsub (exponent (ofGaussian (translated z B one) B) s g) (exponent (ofGaussian z B) s g) ≐
       shift z B s g) :=
  closeUniv 4 (.impI (.impI (exponent_shift _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShiftAlgebra
