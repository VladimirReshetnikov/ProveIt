import IPRADerivations.Analysis.RationalArithmetic.Spans.Pivoting.GaussianRationalPivotSearch

/-!
# Preservation of a column with zero in the selected row

If the chosen row has field value zero in a column, normalizing the row
and using it to eliminate the pivot leaves every value in that column
unchanged. This includes arbitrary raw representations of field zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEliminationZeroColumn

open_ipra
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalHorner (qzero)
open GaussianRationalPivotSearch (flag selected next next_success next_failure flag_cases)
open GaussianRationalRowElimination (pivot inverse normalizedPivot eliminate)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right)
open GaussianRationalSyntheticCoefficientValues (qadd_recode_left qmul_recode_right)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq recode_canonical)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel_one)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem normalized_zero (A i p j : PTm n) (h : Γ ⊢[PRAAx] pivot A i j ≐ qzero) :
    Γ ⊢[PRAAx] normalizedPivot A i p j ≐ qzero :=
  (qmul_recode_right (inverse A i p) (cell A i j)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans (qmul_zero_right _))

theorem eliminated_column_value (A R N i p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R)
    (hj : Γ ⊢[PRAAx] lt j N) (h : Γ ⊢[PRAAx] pivot A i j ≐ qzero) :
    Γ ⊢[PRAAx] cell (eliminate A R N i p) r j ≐ recode (cell A r j) := by
  have nz := normalized_zero A i p j h
  refine .orE (eq_or_ne r i) ?_ ?_
  · have same : (r ≐ i) :: Γ ⊢[PRAAx] cell A r j ≐ cell A i j :=
      entry_congr (entry_congr (.eqRefl A) Prf.hyp0) (.eqRefl j)
    exact (GaussianRationalRowElimination.output_lookup A R N i p r j hr.wk hj.wk).eqTrans
      ((sel_one (eqb_of_eq Prf.hyp0)).eqTrans
        (nz.wk.eqTrans ((recode_congr same).eqTrans h.wk).eqSymm))
  · exact (GaussianRationalRowElimination.eliminated_lookup A R N i p r j hr.wk hj.wk Prf.hyp0).eqTrans
      ((GaussianInverseBinomialRows.difference_negative_product _ _ _).eqTrans
        ((qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _) nz.wk).eqTrans (qmul_zero_right _))).eqTrans
          ((qadd_recode_left _ _).eqSymm.eqTrans
            (GaussianReciprocalHorner.qadd_zero_right _ (recode_canonical _)))))

theorem next_preserves_column (A R N H c p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hj : Γ ⊢[PRAAx] lt j N)
    (h : Γ ⊢[PRAAx] flag A R H c p ≐ one ⟶ pivot A (selected A R H c p) j ≐ qzero) :
    Γ ⊢[PRAAx] pivot (next A R N H c p) r j ≐ pivot A r j := by
  refine .orE (flag_cases A R H c p) ?_ ?_
  · exact recode_congr (entry_congr (entry_congr (next_failure _ _ _ _ _ _ Prf.hyp0) (.eqRefl r)) (.eqRefl j))
  · have e := entry_congr (entry_congr (next_success (Γ := (flag A R H c p ≐ one) :: Γ)
      A R N H c p Prf.hyp0) (.eqRefl r)) (.eqRefl j)
    have value := eliminated_column_value A R N (selected A R H c p) p r j hr.wk hj.wk (.impE h.wk Prf.hyp0)
    exact (recode_congr (e.eqTrans value)).eqTrans (recode_eq _ (recode_canonical _))

theorem actual_preserved_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (lt (var 6) (var 1) ⟶ lt (var 7) (var 2) ⟶
      (flag (var 0) (var 1) (var 3) (var 4) (var 5) ≐ one ⟶
        pivot (var 0) (selected (var 0) (var 1) (var 3) (var 4) (var 5)) (var 7) ≐ qzero) ⟶
      pivot (next (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6) (var 7) ≐ pivot (var 0) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (next_preserves_column _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalEliminationZeroColumn
