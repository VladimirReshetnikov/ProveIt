import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponential

/-!
# Exact odd factorial terms of the finite scalar exponential

With the same even cutoff on the two actual Gaussian scalar sums, their
difference is twice the original odd factorial sum. The formula is an
identity of canonical Gaussian rational codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarExponentialOddTaylor

open_ipra
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalPolynomialExponential (scalarSum scalarBody scalar_sum_zero scalar_sum_succ inverseFactorial scalar_body_at)
open GaussianRationalFiniteSum (sum sum_index_congr sum_canonical add_shuffle)
open GaussianMomentReflection (negative_even_power negative_odd_power negative_right_product)
open GaussianCoefficientNormOrder (qsub_self)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scalarTerm (q j : PTm n) : PTm n := qmul (inverseFactorial j) (power q j)
def oddBody : PTm 2 := scalarTerm (var 1) (succ (two*var 0))
def oddSum (q K : PTm n) : PTm n := sum oddBody K q

ipra_subst oddSum

theorem odd_body_at (q j : PTm n) : inst2 oddBody j q = scalarTerm q (succ (two*j)) := by
  simp [oddBody, scalarTerm, inst2]

theorem odd_sum_succ (q K : PTm n) :
    Γ ⊢[PRAAx] oddSum q (succ K) ≐ qadd (oddSum q K) (scalarTerm q (succ (two*K))) := by
  simpa only [oddSum, odd_body_at] using GaussianRationalFiniteSum.sum_succ (Γ := Γ) oddBody K q

theorem odd_sum_canonical (q K : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (oddSum q K) :=
  sum_canonical _ _ _

theorem even_term (q K : PTm n) :
    Γ ⊢[PRAAx] scalarTerm (qnegative q) (two*K) ≐ scalarTerm q (two*K) :=
  qmul_congr (.eqRefl _) (negative_even_power q K)

theorem odd_term (q K : PTm n) :
    Γ ⊢[PRAAx] scalarTerm (qnegative q) (succ (two*K)) ≐ qnegative (scalarTerm q (succ (two*K))) :=
  (qmul_congr (.eqRefl _) (negative_odd_power q K)).eqTrans (negative_right_product _ _)

private theorem scalar_sum_two_terms (q K : PTm n) :
    Γ ⊢[PRAAx] scalarSum q (two*succ K) ≐
      qadd (qadd (scalarSum q (two*K)) (scalarTerm q (succ (two*K)))) (scalarTerm q (two*succ K)) := by
  have idx : Γ ⊢[PRAAx] two*succ K ≐ succ (succ (two*K)) := by ipra_ring
  have e : Γ ⊢[PRAAx] scalarSum q (two*succ K) ≐ scalarSum q (succ (succ (two*K))) :=
    sum_index_congr scalarBody (congrSucc idx) (.eqRefl _)
  have t : Γ ⊢[PRAAx] scalarTerm q (succ (succ (two*K))) ≐ scalarTerm q (two*succ K) := by
    simpa only [scalar_body_at, scalarTerm] using congrInst2 scalarBody idx.eqSymm (.eqRefl q)
  exact e.eqTrans ((scalar_sum_succ q (succ (two*K))).eqTrans (qadd_congr (scalar_sum_succ q (two*K)) t))

private theorem odd_difference (q K : PTm n) :
    Γ ⊢[PRAAx] qsub (scalarTerm q (succ (two*K))) (scalarTerm (qnegative q) (succ (two*K))) ≐
      qadd (scalarTerm q (succ (two*K))) (scalarTerm q (succ (two*K))) :=
  (qsub_congr (.eqRefl _) (odd_term q K)).eqTrans
    (qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution _ (GaussianRationalHorner.qmul_canonical _ _)))

def oddLaw (q K : PTm n) : Fm PTm n :=
  qsub (scalarSum q (two*K)) (scalarSum (qnegative q) (two*K)) ≐ qadd (oddSum q K) (oddSum q K)

ipra_subst oddLaw

private theorem odd_law_zero (q : PTm n) : Γ ⊢[PRAAx] oddLaw q zero := by
  have idx : Γ ⊢[PRAAx] two*(zero : PTm n) ≐ zero := by ipra_ring
  have e (a : PTm n) : Γ ⊢[PRAAx] scalarSum a (two*zero) ≐ GaussianRationalReciprocal.qone :=
    (sum_index_congr scalarBody (congrSucc idx) (.eqRefl a)).eqTrans (scalar_sum_zero a)
  have z := GaussianRationalFiniteSum.sum_zero (Γ := Γ) oddBody q
  exact (qsub_congr (e q) (e (qnegative q))).eqTrans ((qsub_self _).eqTrans
    ((GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical).eqSymm.eqTrans
      (qadd_congr z.eqSymm z.eqSymm)))

private theorem odd_law_step (q K : PTm n) (ih : Γ ⊢[PRAAx] oddLaw q K) :
    Γ ⊢[PRAAx] oddLaw q (succ K) := by
  let F := scalarSum q (two*K)
  let G := scalarSum (qnegative q) (two*K)
  let a := scalarTerm q (succ (two*K))
  let b := scalarTerm (qnegative q) (succ (two*K))
  let c := scalarTerm q (two*succ K)
  let s := oddSum q K
  have hp := scalar_sum_two_terms (Γ := Γ) q K
  have hn := (scalar_sum_two_terms (Γ := Γ) (qnegative q) K).eqTrans
    (qadd_congr (.eqRefl _) (even_term q (succ K)))
  have common : Γ ⊢[PRAAx] qsub (qadd (qadd F a) c) (qadd (qadd G b) c) ≐ qsub (qadd F a) (qadd G b) :=
    (GaussianNameArithmetic.sum_difference (qadd F a) (qadd G b) c c).eqTrans
      ((qadd_congr (.eqRefl _) (qsub_self c)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qsub_canonical _ _)))
  exact (qsub_congr hp hn).eqTrans (common.eqTrans
    ((GaussianNameArithmetic.sum_difference F G a b).eqTrans
      ((qadd_congr ih (odd_difference q K)).eqTrans
        ((add_shuffle s s a a).eqTrans
          (qadd_congr (odd_sum_succ q K).eqSymm (odd_sum_succ q K).eqSymm)))))

theorem odd_taylor_identity (q K : PTm n) : Γ ⊢[PRAAx] oddLaw q K := by
  have hall : Γ ⊢[PRAAx] .all (oddLaw (Syn.shift q) (var 0)) := by
    ipra_qfind [subst_oddLaw]
    · exact odd_law_zero q
    · exact odd_law_step _ _ Prf.hyp0
  simpa only [subst_oddLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using hall.allE K

theorem actual_scalar_exponential_odd_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (oddLaw (var 0) (var 1)) :=
  closeUniv 2 (odd_taylor_identity _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarExponentialOddTaylor
