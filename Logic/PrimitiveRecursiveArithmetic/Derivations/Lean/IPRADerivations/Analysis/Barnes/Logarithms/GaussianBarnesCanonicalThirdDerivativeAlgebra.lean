import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeStep

/-!
# Exact reciprocal-square expansion for the next Barnes logarithmic derivative

If I−J=d I J, then I²−J²−2d I³=(d I)(J−I)(2I+J).
This identity uses the actual normalized Gaussian arithmetic.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (sum_difference)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (qmul qadd)
open GaussianRationalMetric (qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qmul_associative)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def doubleSquare (i : PTm n) : PTm n := qadd (qmul i i) (qmul i i)

def inverseWeight (i j : PTm n) : PTm n := qadd (qadd i i) j

theorem square_difference (i j : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul i i) (qmul j j) ≐ qmul (qsub i j) (qadd i j) :=
  (product_difference i j i j).eqTrans
    ((qadd_congr (.eqRefl _) (qmul_commutative j (qsub i j))).eqTrans
      (qmul_add (qsub i j) i j).eqSymm)

theorem mixed_difference (i j : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul j (qadd i j)) (doubleSquare i) ≐ qmul (qsub j i) (inverseWeight i j) := by
  let v := qsub j i
  have mixed : Γ ⊢[PRAAx] qsub (qmul j i) (qmul i i) ≐ qmul v i :=
    (qsub_congr (qmul_commutative j i) (.eqRefl _)).eqTrans
      ((multiplication_difference i j i).eqTrans (qmul_commutative i v))
  have sums : Γ ⊢[PRAAx] qadd i (qadd j i) ≐ inverseWeight i j :=
    (qadd_congr (.eqRefl _) (qadd_commutative j i)).eqTrans (qadd_associative i i j).eqSymm
  exact (qsub_congr (qmul_add j i j) (.eqRefl _)).eqTrans
    ((sum_difference (qmul j i) (qmul i i) (qmul j j) (qmul i i)).eqTrans
      ((qadd_congr mixed (square_difference j i)).eqTrans
        ((qmul_add v i (qadd j i)).eqSymm.eqTrans (qmul_congr (.eqRefl _) sums))))

theorem residual (i j d : PTm n) (he : Γ ⊢[PRAAx] qsub i j ≐ qmul (qmul d i) j) :
    Γ ⊢[PRAAx] qsub (qsub (qmul i i) (qmul j j)) (qmul (qmul d i) (doubleSquare i)) ≐
      qmul (qmul d i) (qmul (qsub j i) (inverseWeight i j)) := by
  have expand : Γ ⊢[PRAAx] qsub (qmul i i) (qmul j j) ≐ qmul (qmul d i) (qmul j (qadd i j)) :=
    (square_difference i j).eqTrans
      ((qmul_congr he (.eqRefl _)).eqTrans (qmul_associative (qmul d i) j (qadd i j)))
  exact (qsub_congr expand (.eqRefl _)).eqTrans
    ((multiplication_difference (qmul d i) (qmul j (qadd i j)) (doubleSquare i)).eqTrans
      (qmul_congr (.eqRefl _) (mixed_difference i j)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeAlgebra
