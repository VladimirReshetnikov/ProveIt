import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalParityPower
import IPRADerivations.Analysis.Logarithm.Robin.GaussianRobinLogarithmParity
import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentIntegrand

/-!
# Exact reflected Gaussian polynomial rows

The actual normalized rational power loop has even/odd reflection at
all internal indices. Both reflected Gaussian rows retain the SAME
original decay sample at the squared positive argument. Their odd
weighted pair cancels exactly, for arbitrary numerical observation,
weight and moment index. This is finite reflection algebra; convergence
and identification of a whole-line integral remain separate suppliers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMomentReflection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qadd qzero ofGaussian_represents canonical_unique represents_congr)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qadd_congr)
open GaussianRationalReciprocal (power power_canonical)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalMatrixFiniteSums (negative_as_minusOne)
open GaussianRationalParityPower (negative_power parity_succ)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianPositiveRationalLogarithm (fraction)
open ComplexLogarithmRemainder (oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem parity_even (N : PTm n) : Γ ⊢[PRAAx] parityPoint (two*N) ≐ qone :=
  canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) qone_canonical (le_refl one)
    (represents_congr (.eqRefl _) (GaussianRobinLogarithmParity.parity_even N) (.eqRefl _)
      (ofGaussian_represents _ _ (le_refl one))) (ofGaussian_represents _ _ (le_refl one))
theorem parity_odd (N : PTm n) : Γ ⊢[PRAAx] parityPoint (succ (two*N)) ≐ qnegative qone :=
  (parity_succ (two*N)).eqTrans (GaussianInverseBinomialRows.negative_congr (parity_even N))

theorem negative_even_power (t N : PTm n) : Γ ⊢[PRAAx] power (qnegative t) (two*N) ≐ power t (two*N) :=
  (negative_power t (two*N)).eqTrans ((qmul_congr (parity_even N) (.eqRefl _)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ (power_canonical _ _))))
theorem negative_odd_power (t N : PTm n) : Γ ⊢[PRAAx]
    power (qnegative t) (succ (two*N)) ≐ qnegative (power t (succ (two*N))) :=
  (negative_power t (succ (two*N))).eqTrans ((qmul_congr (parity_odd N) (.eqRefl _)).eqTrans (negative_as_minusOne _).eqSymm)

def row (p M t a b c d : PTm n) : PTm n := qmul (power t M) (ap2 decayF p (decayData (c*(a*a)) (d*(b*b))))
@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (p M t a b c d : PTm n) :
    Syn.subst σ (row p M t a b c d) = row (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ t)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [row]

theorem even_row (p N a b c d : PTm n) : Γ ⊢[PRAAx]
    row p (two*N) (qnegative (fraction a b)) a b c d ≐ row p (two*N) (fraction a b) a b c d :=
  qmul_congr (negative_even_power _ N) (.eqRefl _)
theorem odd_row (p N a b c d : PTm n) : Γ ⊢[PRAAx]
    row p (succ (two*N)) (qnegative (fraction a b)) a b c d ≐ qnegative (row p (succ (two*N)) (fraction a b) a b c d) :=
  (qmul_congr (negative_odd_power _ N) (.eqRefl _)).eqTrans (GaussianInverseBinomialRows.negative_product _ _).eqSymm

theorem negative_right_product (w z : PTm n) : Γ ⊢[PRAAx] qmul w (qnegative z) ≐ qnegative (qmul w z) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianInverseBinomialRows.negative_product z w).eqSymm.eqTrans
      (GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative z w)))

theorem odd_weighted_pair (p N a b c d w : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul w (row p (succ (two*N)) (fraction a b) a b c d))
      (qmul w (row p (succ (two*N)) (qnegative (fraction a b)) a b c d)) ≐ qzero :=
  (qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (odd_row p N a b c d)).eqTrans (negative_right_product _ _))).eqTrans
    (GaussianCoefficientNormOrder.qsub_self _)

theorem actual_original_even_Gaussian_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (row (var 0) (two*(var 1)) (qnegative (fraction (var 2) (var 3))) (var 2) (var 3) (var 4) (var 5) ≐
      row (var 0) (two*(var 1)) (fraction (var 2) (var 3)) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (even_row _ _ _ _ _ _)
theorem actual_original_odd_Gaussian_weighted_pair_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (qadd (qmul (var 6) (row (var 0) (succ (two*(var 1))) (fraction (var 2) (var 3)) (var 2) (var 3) (var 4) (var 5)))
      (qmul (var 6) (row (var 0) (succ (two*(var 1))) (qnegative (fraction (var 2) (var 3))) (var 2) (var 3) (var 4) (var 5))) ≐ qzero) :=
  closeUniv 7 (odd_weighted_pair _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianMomentReflection
