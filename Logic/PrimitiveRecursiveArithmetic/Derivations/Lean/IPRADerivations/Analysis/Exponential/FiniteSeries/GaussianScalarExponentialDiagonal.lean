import IPRADerivations.Analysis.Exponential.FiniteSeries.GaussianRationalExponentialProductCoefficients
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientRecursion

/-!
# The diagonal Cauchy sums of the original scalar exponential

The degree-e diagonal uses the literal original scalar terms at indices
i and e-i. Weighting each summand by e splits its two natural weights.
The two resulting finite sums reindex to the preceding diagonal using
the factorial recurrence, with a zero contribution at each boundary.
Quantifier-free induction then identifies every computed diagonal with
the original scalar term at the sum of the arguments.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarExponentialDiagonal

open_ipra
open GaussianRationalHorner (qzero qadd qmul canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr qzero_add)
open GaussianRationalPolynomialExponential (inverseFactorial inverse_factorial_zero scalarBody scalarSum scalar_body_at)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalNaturalScale (natScale natScale_add natScale_product natScale_congr natScale_zero
  natScale_as_product naturalPoint)
open GaussianRationalWeightedCoefficientConvolution (left_scale_product)
open GaussianRationalFactorialEulerSums (inverse_factorial_scale)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalCoefficientRecursion (scale_cancel)
open GaussianReciprocalHorner (qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (q e : PTm n) : PTm n := qmul (inverseFactorial e) (power q e)

ipra_subst coefficient

theorem original_term (q e : PTm n) : inst2 scalarBody e q = coefficient q e := scalar_body_at q e

theorem coefficient_canonical (q e : PTm n) : Γ ⊢[PRAAx] canonical (coefficient q e) :=
  GaussianRationalHorner.qmul_canonical _ _

theorem coefficient_zero (q : PTm n) : Γ ⊢[PRAAx] coefficient q zero ≐ qone :=
  (qmul_congr inverse_factorial_zero (power_zero q)).eqTrans (qmul_one_right _ qone_canonical)

theorem coefficient_succ_weighted (q e : PTm n) : Γ ⊢[PRAAx]
    natScale (succ e) (coefficient q (succ e)) ≐ qmul q (coefficient q e) := by
  unfold coefficient
  exact (left_scale_product _ _ _).eqTrans
    ((qmul_congr (inverse_factorial_scale e) (power_succ q e)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        (qmul_commutative _ _)))

def data (u v e : PTm n) : PTm n := pairT u (pairT v e)

def term (u v e i : PTm n) : PTm n := qmul (coefficient u i) (coefficient v (monus e i))

def leftTerm (u v e i : PTm n) : PTm n := qmul (natScale i (coefficient u i)) (coefficient v (monus e i))

def rightTerm (u v e i : PTm n) : PTm n := qmul (coefficient u i) (natScale (monus e i) (coefficient v (monus e i)))

def termBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def leftBody : PTm 2 := leftTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def rightBody : PTm 2 := rightTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

def diagonal (u v e : PTm n) : PTm n := GaussianRationalFiniteSum.sum termBody (succ e) (data u v e)
def leftSum (u v e : PTm n) : PTm n := GaussianRationalFiniteSum.sum leftBody (succ e) (data u v e)
def rightSum (u v e : PTm n) : PTm n := GaussianRationalFiniteSum.sum rightBody (succ e) (data u v e)

ipra_subst data

ipra_subst term

ipra_subst leftTerm

ipra_subst rightTerm

ipra_subst diagonal

ipra_subst leftSum

ipra_subst rightSum

theorem body_at (f : PTm 4) (u v e i : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![fstT (data u v e),fstT (sndT (data u v e)),sndT (sndT (data u v e)),i] f ≐
      Syn.subst ![u,v,e,i] f :=
  Prf.eqCongr f (fun j => by
    fin_cases j
    · exact fst_pair _ _
    · exact (snd_pair _ _).fstE
    · exact (snd_pair _ _).sndE
    · exact .eqRefl _)

theorem term_at (u v e i : PTm n) : Γ ⊢[PRAAx] inst2 termBody i (data u v e) ≐ term u v e i := by
  simpa [inst2,termBody] using (body_at (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3)) u v e i)

theorem left_at (u v e i : PTm n) : Γ ⊢[PRAAx] inst2 leftBody i (data u v e) ≐ leftTerm u v e i := by
  simpa [inst2,leftBody] using (body_at (Γ := Γ) (leftTerm (var 0) (var 1) (var 2) (var 3)) u v e i)

theorem right_at (u v e i : PTm n) : Γ ⊢[PRAAx] inst2 rightBody i (data u v e) ≐ rightTerm u v e i := by
  simpa [inst2,rightBody] using (body_at (Γ := Γ) (rightTerm (var 0) (var 1) (var 2) (var 3)) u v e i)

theorem weight_term (u v e i : PTm n) (hi : Γ ⊢[PRAAx] le i e) :
    Γ ⊢[PRAAx] natScale e (term u v e i) ≐ qadd (leftTerm u v e i) (rightTerm u v e i) :=
  (natScale_congr (eq_add_of_le hi) (.eqRefl _)).eqTrans
    ((natScale_add i (monus e i) (term u v e i)).eqTrans
      (qadd_congr (left_scale_product _ _ _) (natScale_product _ _ _).eqSymm))

theorem weight_entry (u v e i : PTm n) (hi : Γ ⊢[PRAAx] le i e) :
    Γ ⊢[PRAAx] inst2 (GaussianRationalFiniteSum.multiplyBody termBody) i (pairT (naturalPoint e) (data u v e)) ≐
      inst2 (GaussianRationalFiniteSum.addBody leftBody rightBody) i (data u v e) := by
  rw [GaussianRationalFiniteSum.inst2_addBody]
  exact (GaussianRationalFiniteSum.multiply_body_at _ _ _ _).eqTrans
    ((qmul_congr (.eqRefl _) (term_at u v e i)).eqTrans
      ((natScale_as_product _ _).eqSymm.eqTrans
        ((weight_term u v e i hi).eqTrans (qadd_congr (left_at u v e i) (right_at u v e i)).eqSymm)))

theorem diagonal_weighted (u v e : PTm n) : Γ ⊢[PRAAx]
    natScale e (diagonal u v e) ≐ qadd (leftSum u v e) (rightSum u v e) := by
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      (GaussianRationalFiniteSum.multiplyBody termBody) (GaussianRationalFiniteSum.addBody leftBody rightBody) (succ e)
      (pairT (naturalPoint e) (data u v e)) (data u v e) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,subst_pairT,
      GaussianRationalNaturalScale.subst_naturalPoint,subst_data] using
      weight_entry (Syn.shift u) (Syn.shift v) (Syn.shift e) (var 0) hi
  exact (natScale_as_product e (diagonal u v e)).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply termBody (naturalPoint e) (succ e) (data u v e)).eqSymm.eqTrans
      ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries).eqTrans
        (GaussianRationalFiniteSum.sum_add leftBody rightBody (succ e) (data u v e))))

theorem coefficient_congr {q r e f : PTm n} (hq : Γ ⊢[PRAAx] q ≐ r) (he : Γ ⊢[PRAAx] e ≐ f) :
    Γ ⊢[PRAAx] coefficient q e ≐ coefficient r f := by
  ipra_congr (coefficient (var 0) (var 1) : PTm 2) with [hq, he]

theorem left_zero (u v e : PTm n) : Γ ⊢[PRAAx] leftTerm u v e zero ≐ qzero :=
  (qmul_congr (natScale_zero _) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)

theorem right_last (u v e : PTm n) : Γ ⊢[PRAAx] rightTerm u v e e ≐ qzero :=
  (qmul_congr (.eqRefl _) ((natScale_congr (monus_self e) (.eqRefl _)).eqTrans (natScale_zero _))).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem left_step (u v e i : PTm n) : Γ ⊢[PRAAx]
    leftTerm u v (succ e) (succ i) ≐ qmul u (term u v e i) :=
  (qmul_congr (coefficient_succ_weighted u i) (coefficient_congr (.eqRefl _) (succ_monus_succ e i))).eqTrans
    (GaussianReciprocalHorner.qmul_associative _ _ _)

theorem right_step (u v e i : PTm n) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    rightTerm u v (succ e) i ≐ qmul v (term u v e i) := by
  have eq := LogarithmExponentialCoefficients.monus_succ_le hi
  exact (qmul_congr (.eqRefl _) ((natScale_congr eq (coefficient_congr (.eqRefl _) eq)).eqTrans
    (coefficient_succ_weighted v (monus e i)))).eqTrans
      (GaussianRationalExponentialProductCoefficients.scalar_shuffle _ _ _)

theorem left_sum_step (u v e : PTm n) : Γ ⊢[PRAAx] leftSum u v (succ e) ≐ qmul u (diagonal u v e) := by
  let D := data u v (succ e)
  let E := data u v e
  let f := LeanProofs.IPRA.shiftBody leftBody
  let g := GaussianRationalFiniteSum.multiplyBody termBody
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual f g (succ e) D (pairT u E) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have step : Δ ⊢[PRAAx] inst2 f (var 0) (data (Syn.shift u) (Syn.shift v) (succ (Syn.shift e))) ≐
        inst2 g (var 0) (pairT (Syn.shift u) (data (Syn.shift u) (Syn.shift v) (Syn.shift e))) := by
      rw [show f = LeanProofs.IPRA.shiftBody leftBody from rfl,
        LeanProofs.IPRA.inst2_shiftBody]
      exact (left_at _ _ _ _).eqTrans ((left_step _ _ _ _).eqTrans
        ((GaussianRationalFiniteSum.multiply_body_at _ _ _ _).eqTrans (qmul_congr (.eqRefl _) (term_at _ _ _ _))).eqSymm)
    simpa only [Δ,D,E,Syn.shift,subst_data,subst_pairT,ConciseIPRA.PTm.subst_succ] using step
  have first := (left_at (Γ := Γ) u v (succ e) zero).eqTrans (left_zero u v (succ e))
  have tail := (GaussianRationalFiniteSum.sum_congr_bounded f g (succ e) D (pairT u E) entries).eqTrans
    (GaussianRationalFiniteSum.sum_multiply termBody u (succ e) E)
  exact (GaussianRationalFiniteSum.sum_shift_first leftBody (succ e) D).eqTrans
    ((qadd_congr first tail).eqTrans (qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem right_sum_step (u v e : PTm n) : Γ ⊢[PRAAx] rightSum u v (succ e) ≐ qmul v (diagonal u v e) := by
  let D := data u v (succ e)
  let E := data u v e
  let g := GaussianRationalFiniteSum.multiplyBody termBody
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual rightBody g (succ e) D (pairT v E) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have step : Δ ⊢[PRAAx] inst2 rightBody (var 0) (data (Syn.shift u) (Syn.shift v) (succ (Syn.shift e))) ≐
        inst2 g (var 0) (pairT (Syn.shift v) (data (Syn.shift u) (Syn.shift v) (Syn.shift e))) :=
      (right_at _ _ _ _).eqTrans ((right_step _ _ _ _ hi).eqTrans
        ((GaussianRationalFiniteSum.multiply_body_at _ _ _ _).eqTrans (qmul_congr (.eqRefl _) (term_at _ _ _ _))).eqSymm)
    simpa only [Δ,D,E,Syn.shift,subst_data,subst_pairT,ConciseIPRA.PTm.subst_succ] using step
  have head := (GaussianRationalFiniteSum.sum_congr_bounded rightBody g (succ e) D (pairT v E) entries).eqTrans
    (GaussianRationalFiniteSum.sum_multiply termBody v (succ e) E)
  have last := (right_at (Γ := Γ) u v (succ e) (succ e)).eqTrans (right_last u v (succ e))
  exact (GaussianRationalFiniteSum.sum_succ rightBody (succ e) D).eqTrans
    ((qadd_congr head last).eqTrans (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem diagonal_succ_weighted (u v e : PTm n) : Γ ⊢[PRAAx]
    natScale (succ e) (diagonal u v (succ e)) ≐ qmul (qadd u v) (diagonal u v e) := by
  have distributive : Γ ⊢[PRAAx] qmul (qadd u v) (diagonal u v e) ≐
      qadd (qmul u (diagonal u v e)) (qmul v (diagonal u v e)) :=
    (qmul_commutative _ _).eqTrans ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (qmul_commutative _ _) (qmul_commutative _ _)))
  exact (diagonal_weighted u v (succ e)).eqTrans
    ((qadd_congr (left_sum_step u v e) (right_sum_step u v e)).eqTrans distributive.eqSymm)

theorem diagonal_zero (u v : PTm n) : Γ ⊢[PRAAx] diagonal u v zero ≐ qone := by
  have e : Γ ⊢[PRAAx] term u v zero zero ≐ qone :=
    (qmul_congr (coefficient_zero u) ((coefficient_congr (.eqRefl _) (monus_self zero)).eqTrans
      (coefficient_zero v))).eqTrans (qmul_one_right _ qone_canonical)
  exact (GaussianRationalFiniteSum.sum_succ termBody zero (data u v zero)).eqTrans
    ((qadd_congr (GaussianRationalFiniteSum.sum_zero _ _) ((term_at _ _ _ _).eqTrans e)).eqTrans (qzero_add _ qone_canonical))

def diagonalLaw (u v e : PTm n) : Fm PTm n := diagonal u v e ≐ coefficient (qadd u v) e

ipra_subst diagonalLaw

theorem diagonal_law_step (u v e : PTm n) (h : Γ ⊢[PRAAx] diagonalLaw u v e) :
    Γ ⊢[PRAAx] diagonalLaw u v (succ e) :=
  scale_cancel (succ e) _ _ (zero_lt_succ e) (GaussianRationalFiniteSum.sum_canonical _ _ _) (coefficient_canonical _ _)
    ((diagonal_succ_weighted u v e).eqTrans ((qmul_congr (.eqRefl _) h).eqTrans
      (coefficient_succ_weighted (qadd u v) e).eqSymm))

theorem diagonal_at_sum (u v e : PTm n) : Γ ⊢[PRAAx] diagonal u v e ≐ coefficient (qadd u v) e := by
  have all : Γ ⊢[PRAAx] .all (diagonalLaw (Syn.shift u) (Syn.shift v) (var 0)) := by
    ipra_qfind [subst_diagonalLaw]
    · exact (diagonal_zero u v).eqTrans (coefficient_zero (qadd u v)).eqSymm
    · exact diagonal_law_step _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] diagonalLaw u v e
  simpa only [subst_diagonalLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE e

def triangularBody : PTm 2 := diagonal (fstT (var 1)) (sndT (var 1)) (var 0)

def triangularSum (u v K : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum triangularBody (succ K) (pairT u v)

ipra_subst triangularSum

theorem triangular_body_at (u v e : PTm n) : Γ ⊢[PRAAx] inst2 triangularBody e (pairT u v) ≐ diagonal u v e := by
  ipra_congr (diagonal (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl e] using [triangularBody, inst2]

theorem triangular_exponential (u v K : PTm n) : Γ ⊢[PRAAx]
    triangularSum u v K ≐ scalarSum (qadd u v) K := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift
  have eq : Δ ⊢[PRAAx] inst2 triangularBody (var 0) (pairT (Syn.shift u) (Syn.shift v)) ≐
      inst2 scalarBody (var 0) (qadd (Syn.shift u) (Syn.shift v)) := by
    rw [original_term]
    exact (triangular_body_at _ _ _).eqTrans (diagonal_at_sum _ _ _)
  simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalHorner.subst_qadd,ConciseIPRA.PTm.subst_succ] using eq

def triangularF : PR 3 := PTm.toPR (triangularSum (var 0) (var 1) (var 2))
def run (u v K : PTm n) : PTm n := ConciseIPRA.PTm.app triangularF ![u,v,K]

theorem program_at (u v K : PTm n) : Γ ⊢[PRAAx] run u v K ≐ triangularSum u v K := by
  simpa [run,triangularF] using toPR_eq (Γ := Γ) (triangularSum (var 0) (var 1) (var 2) : PTm 3) ![u,v,K]

theorem original_scalar_coefficient_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (natScale (succ (var 1)) (coefficient (var 0) (succ (var 1))) ≐ qmul (var 0) (coefficient (var 0) (var 1))) :=
  closeUniv 2 (coefficient_succ_weighted _ _)

theorem actual_diagonal_weighted_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (natScale (succ (var 2)) (diagonal (var 0) (var 1) (succ (var 2))) ≐
      qmul (qadd (var 0) (var 1)) (diagonal (var 0) (var 1) (var 2))) :=
  closeUniv 3 (diagonal_succ_weighted _ _ _)

theorem actual_scalar_exponential_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (diagonal (var 0) (var 1) (var 2) ≐ inst2 scalarBody (var 2) (qadd (var 0) (var 1))) := by
  rw [original_term]
  exact closeUniv 3 (diagonal_at_sum _ _ _)

theorem actual_triangular_exponential_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ triangularSum (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

theorem original_returned_triangular_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ scalarSum (qadd (var 0) (var 1)) (var 2)) :=
  closeUniv 3 ((program_at _ _ _).eqTrans (triangular_exponential _ _ _))

end LeanProofs.IPRA.Analysis.GaussianScalarExponentialDiagonal
