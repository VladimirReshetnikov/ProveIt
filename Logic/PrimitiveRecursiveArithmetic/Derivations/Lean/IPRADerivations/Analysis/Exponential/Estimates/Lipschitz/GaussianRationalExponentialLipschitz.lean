import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTail
import IPRADerivations.Analysis.Polynomials.Coefficients.Operations.GaussianPolynomialCoefficientDifferences
import IPRADerivations.Analysis.Exponential.FiniteSeries.ExponentialSeries

/-!
# Uniform Lipschitz bounds for the original finite scalar exponential

On the original Euclidean unit disk, every actual scalarSum has
Lipschitz constant3. The real power-difference theorem bounds each
factorial-weighted difference. A genuine QF invariant for the SAME
scalarSum compares its actual difference with A*en(k)/(B*k!).
The existing native en_upper supplies the uniform constant. No
completed exponential, derivative or output law is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialLipschitz

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power bound_congr bounded_product bounded_sum)
open GaussianRationalPolynomialExponential (inverseFactorial factorial_positive scalarSum scalarBody)
open ExponentialSeries (en)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termDifference (u v e : PTm n) : PTm n := qsub
  (qmul (inverseFactorial e) (power u e)) (qmul (inverseFactorial e) (power v e))
def difference (u v K : PTm n) : PTm n := qsub (scalarSum u K) (scalarSum v K)
ipra_subst termDifference
ipra_subst difference

theorem difference_zero (u v : PTm n) : Γ ⊢[PRAAx] difference u v zero ≐ qzero :=
  (qsub_congr (GaussianRationalPolynomialExponential.scalar_sum_zero u)
    (GaussianRationalPolynomialExponential.scalar_sum_zero v)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem difference_succ (u v k : PTm n) : Γ ⊢[PRAAx] difference u v (succ k) ≐
    qadd (difference u v k) (termDifference u v (succ k)) :=
  (qsub_congr (GaussianRationalPolynomialExponential.scalar_sum_succ u k)
    (GaussianRationalPolynomialExponential.scalar_sum_succ v k)).eqTrans
      (GaussianPolynomialCoefficientDifferences.scalar_sum_difference _ _ _ _)

theorem difference_one (u v : PTm n) : Γ ⊢[PRAAx] difference u v one ≐ termDifference u v one :=
  (difference_succ u v zero).eqTrans ((qadd_congr (difference_zero u v) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qsub_canonical _ _)))

theorem term_bound (u v A B e : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    bounded (termDifference u v e) (e*A) (fact e*B) := by
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial e) one (fact e) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (factorial_positive e)
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm e).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  exact bound_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _).eqSymm
    (one_mul _) (.eqRefl _)
    (bounded_product _ _ _ _ _ _ (factorial_positive e) hB inv
      (GaussianRationalPowerDifference.unit_disk_power_difference u v A B e hB hu hv hd))

def boundLaw (u v A B k : PTm n) : Fm PTm n := bounded (difference u v (succ k)) (A*en k) (B*fact k)
ipra_subst boundLaw [en, fact]

theorem bound_zero (u v A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx] boundLaw u v A B zero := by
  have ee := natEq (ExponentialSeries.en_zero (Γ := Γ))
  have f0 := natEq (fact_zero (Γ := Γ) zero)
  have f1 := natEq (fact_succ (Γ := Γ) zero zero)
  have hn : Γ ⊢[PRAAx] one*A ≐ A*en zero := by apply deriveNat; ipra_simps; rw [ee]; ring
  have hb : Γ ⊢[PRAAx] fact one*B ≐ B*fact zero := by apply deriveNat; ipra_simps; rw [f1,f0]; ring
  exact bound_congr (difference_one u v).eqSymm hn hb (term_bound u v A B one hB hu hv hd)

theorem bound_step (u v A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) (ih : Γ ⊢[PRAAx] boundLaw u v A B k) : Γ ⊢[PRAAx] boundLaw u v A B (succ k) := by
  have pos := positive_product (Γ := Γ) B (fact k) hB (factorial_positive k)
  have termPos := positive_product (Γ := Γ) (fact (succ (succ k))) B (factorial_positive _) hB
  have combined := bounded_sum _ _ _ _ _ _ pos termPos ih (term_bound u v A B (succ (succ k)) hB hu hv hd)
  have radius : Γ ⊢[PRAAx] le
      ((A*en k*(fact (succ (succ k))*B)+(succ (succ k)*A)*(B*fact k))*(B*fact (succ k)))
      ((A*en (succ k))*((B*fact k)*(fact (succ (succ k))*B))) := by
    have ee := natEq (ExponentialSeries.en_succ (Γ := Γ) k)
    have f1 := natEq (fact_succ (Γ := Γ) k zero)
    have f2 := natEq (fact_succ (Γ := Γ) (succ k) zero)
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; ipra_simps; rw [ee,f2,f1]; ring
  exact bound_congr (difference_succ u v (succ k)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ pos termPos)
      (positive_product _ _ hB (factorial_positive _)) radius combined)

theorem prefix_bound (u v A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx] boundLaw u v A B k := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have us : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift u) one one := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) one one := by simpa [Fm.shift,Syn.shift] using hv.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (boundLaw (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using bound_zero u v A B hB hu hv hd
    · simp only [subst_boundLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact bound_step _ _ _ _ _ bs.wk us.wk vs.wk ds.wk Prf.hyp0
  simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem en_bound_succ (k : PTm n) : Γ ⊢[PRAAx] le (en (succ k)) (num 3*fact (succ k)) := by
  apply mul_le_cancel (d' := k)
  exact le_congr (.eqRefl _) (by ipra_ring)
    (le_trans (le_add_right _ one) (ExponentialSeries.en_upper k))

theorem en_bound (k : PTm n) : Γ ⊢[PRAAx] le (en k) (num 3*fact k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have old : (k ≐ zero) :: Γ ⊢[PRAAx] le (en zero) (num 3*fact zero) := by
      refine le_of_eq_add (d := two) ?_
      have e := natEq (ExponentialSeries.en_zero (Γ := (k ≐ zero) :: Γ))
      have f := natEq (fact_zero (Γ := (k ≐ zero) :: Γ) zero)
      apply deriveNat; ipra_simps; rw [e,f]; ring
    exact le_congr (congrAp2 ExponentialSeries.enF Prf.hyp0 (.eqRefl zero)).eqSymm
      (congrMul (.eqRefl _) (congrAp2 factF Prf.hyp0 (.eqRefl zero))).eqSymm old
  · exact le_congr (congrAp2 ExponentialSeries.enF Prf.hyp0 (.eqRefl zero)).eqSymm
      (congrMul (.eqRefl _) (congrAp2 factF Prf.hyp0 (.eqRefl zero))).eqSymm (en_bound_succ (pred k))

theorem difference_congr {u v K L : PTm n} (h : Γ ⊢[PRAAx] K ≐ L) : Γ ⊢[PRAAx] difference u v K ≐ difference u v L :=
  qsub_congr (GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc h) (.eqRefl u))
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc h) (.eqRefl v))

/-- Uniform finite exponential Lipschitz theorem at every numerical
cutoff, from only original query disks and original query distance. -/
theorem scalar_sum_lipschitz (u v A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum u K) (scalarSum v K) (num 3*A) B := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact bound_congr ((difference_congr Prf.hyp0).eqTrans (difference_zero u v)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded _ _ hB.wk)
  · have hp : (K ≐ succ (pred K)) :: Γ ⊢[PRAAx] boundLaw u v A B (pred K) :=
      prefix_bound u v A B (pred K) hB.wk hu.wk hv.wk hd.wk
    have radius : (K ≐ succ (pred K)) :: Γ ⊢[PRAAx]
        le ((A*en (pred K))*B) ((num 3*A)*(B*fact (pred K))) := le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl (A*B)) (en_bound (Γ := (K ≐ succ (pred K)) :: Γ) (pred K)))
    exact bound_congr (difference_congr Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB.wk (factorial_positive _))
        hB.wk radius hp)

/-! Actual PR5 values, difference and genuine uniform metric budget. -/
def output (u v A B K : PTm n) : PTm n := pairT (scalarSum u K)
  (pairT (scalarSum v K) (pairT (difference u v K) (pairT (num 3*A) B)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (u v A B K : PTm n) : PTm n := PTm.app outputF ![u,v,A,B,K]
ipra_subst output
ipra_subst run

theorem program_at (u v A B K : PTm n) : Γ ⊢[PRAAx] run u v A B K ≐ output u v A B K := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![u,v,A,B,K]
theorem returned_left (u v A B K : PTm n) : Γ ⊢[PRAAx] fstT (run u v A B K) ≐ scalarSum u K :=
  (program_at _ _ _ _ _).fstE
theorem returned_tail (u v A B K : PTm n) : Γ ⊢[PRAAx] sndT (run u v A B K) ≐
    pairT (scalarSum v K) (pairT (difference u v K) (pairT (num 3*A) B)) :=
  (program_at _ _ _ _ _).sndE
theorem returned_right (u v A B K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run u v A B K)) ≐ scalarSum v K :=
  (returned_tail _ _ _ _ _).fstE
theorem returned_suffix (u v A B K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run u v A B K)) ≐
    pairT (difference u v K) (pairT (num 3*A) B) :=
  (returned_tail _ _ _ _ _).sndE
theorem returned_difference (u v A B K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run u v A B K))) ≐ difference u v K :=
  (returned_suffix _ _ _ _ _).fstE
theorem returned_pair (u v A B K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run u v A B K))) ≐ pairT (num 3*A) B :=
  (returned_suffix _ _ _ _ _).sndE
theorem returned_numerator (u v A B K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run u v A B K)))) ≐ num 3*A :=
  (returned_pair _ _ _ _ _).fstE
theorem returned_denominator (u v A B K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run u v A B K)))) ≐ B :=
  (returned_pair _ _ _ _ _).sndE
theorem returned_bound (u v A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (sndT (run u v A B K))))
      (fstT (sndT (sndT (sndT (run u v A B K))))) (sndT (sndT (sndT (sndT (run u v A B K))))) :=
  bound_congr (returned_difference _ _ _ _ _).eqSymm (returned_numerator _ _ _ _ _).eqSymm
    (returned_denominator _ _ _ _ _).eqSymm (scalar_sum_lipschitz u v A B K hB hu hv hd)
theorem returned_distance (u v A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u one one) (hv : Γ ⊢[PRAAx] bounded v one one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run u v A B K)) (fstT (sndT (run u v A B K)))
      (fstT (sndT (sndT (sndT (run u v A B K))))) (sndT (sndT (sndT (sndT (run u v A B K))))) :=
  GaussianRationalDistanceOrder.distance_congr (returned_left _ _ _ _ _).eqSymm (returned_right _ _ _ _ _).eqSymm
    (returned_numerator _ _ _ _ _).eqSymm (returned_denominator _ _ _ _ _).eqSymm (scalar_sum_lipschitz u v A B K hB hu hv hd)

theorem original_unit_disk_factorial_term_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (termDifference (var 0) (var 1) (var 4)) (var 4*var 2) (fact (var 4)*var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (term_bound _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_scalar_exponential_prefix_difference_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      boundLaw (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (prefix_bound _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem native_factorial_exponential_majorant_three_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (en (var 0)) (num 3*fact (var 0))) := closeUniv 1 (en_bound _)
theorem original_unit_disk_scalar_exponential_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (scalarSum (var 0) (var 4)) (scalarSum (var 1) (var 4)) (num 3*var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (scalar_sum_lipschitz _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_scalar_exponential_lipschitz_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem returned_scalar_exponential_difference_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_bound _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem returned_scalar_exponential_lipschitz_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) one one ⟶ bounded (var 1) one one ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_distance _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_zero_cutoff_scalar_exponential_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (difference (var 0) (var 1) zero ≐ qzero) := closeUniv 2 (difference_zero _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialLipschitz
