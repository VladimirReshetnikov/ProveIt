import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminant
import IPRADerivations.Analysis.Polynomials.Determinants.Multilinearity.GaussianPolynomialColumnAlternation
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport
import IPRADerivations.Foundations.RuntimeWordSorting

/-!
# Actual scalar column selection by numerical words

The stored selected-column table is passed to the SAME polynomial determinant
through its actual scalar lift. Adjacent alternation and the genuine numerical
sorting program derive its normal form: a permutation word contributes its
actual sign times the original scalar determinant, and a repeated-column word
contributes zero. All dimensions, words, indices and data are numerical.
No permutation, sign, evaluator, sorting or determinant output law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarColumnSelection

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical canonical_unique represents_congr evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical qzero_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric
  (qnegative qnegative_canonical qnegative_represents)
open LeanProofs.IPRA.Analysis.GaussianInverseBinomialRows (negative_congr negative_product)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell signPoint sign_even sign_odd)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (table table_lookup)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The position i chooses the original COLUMN digit_i, never a row value. -/
def data (A m w : PTm n) : PTm n := pairT A (pairT m w)
def columnBody : PTm 3 := cell (fstT (var 2)) (var 0)
  (Foundations.RuntimePermutationWords.digit (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 1))
def columns (A m w : PTm n) : PTm n := table columnBody m m (data A m w)
def selectedDet (A m w : PTm n) : PTm n := GaussianScalarDeterminant.scalarDet (columns A m w) m
def signedSelection (A m w : PTm n) : PTm n := qmul (signPoint m w) (selectedDet A m w)
def expected (A m w : PTm n) : PTm n := Foundations.GuardedTotalization.sel
  (Foundations.RuntimePermutationWords.permutationBit m w)
  (qmul (signPoint m w) (GaussianScalarDeterminant.scalarDet A m)) qzero
ipra_subst data
ipra_subst columns
ipra_subst selectedDet
ipra_subst signedSelection
ipra_subst expected [Foundations.GuardedTotalization.sel]

theorem cell_congr {A B r s i j : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hr : Γ ⊢[PRAAx] r ≐ s) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] cell A r i ≐ cell B s j :=
  Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr hA hr) hi
theorem columns_congr {A B m d w v : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hm : Γ ⊢[PRAAx] m ≐ d) (hw : Γ ⊢[PRAAx] w ≐ v) : Γ ⊢[PRAAx] columns A m w ≐ columns B d v := by
  ipra_congr (columns (var 0) (var 1) (var 2) : PTm 3) with [hA, hm, hw]
theorem selected_det_congr {A B m d w v : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hm : Γ ⊢[PRAAx] m ≐ d) (hw : Γ ⊢[PRAAx] w ≐ v) : Γ ⊢[PRAAx] selectedDet A m w ≐ selectedDet B d v := by
  ipra_congr (selectedDet (var 0) (var 1) (var 2) : PTm 3) with [hA, hm, hw]
theorem signed_selection_congr {A B m d w v : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hm : Γ ⊢[PRAAx] m ≐ d) (hw : Γ ⊢[PRAAx] w ≐ v) : Γ ⊢[PRAAx] signedSelection A m w ≐ signedSelection B d v :=
  qmul_congr (GaussianDeterminantSignTransport.sign_congr hm hw) (selected_det_congr hA hm hw)
theorem columns_length (A m w : PTm n) : Γ ⊢[PRAAx] length (columns A m w) ≐ m :=
  GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem columns_row_length (A m w r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (columns A m w) r) ≐ m := GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ hr
theorem columns_lookup (A m w r i : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    cell (columns A m w) r i ≐ cell A r (Foundations.RuntimePermutationWords.digit m w i) := by
  have e : Γ ⊢[PRAAx] cell (columns A m w) r i ≐ cell (fstT (data A m w)) r
      (Foundations.RuntimePermutationWords.digit (fstT (sndT (data A m w))) (sndT (sndT (data A m w))) i) := by
    simpa [columns,columnBody] using table_lookup columnBody m m (data A m w) r i hr hi
  exact e.eqTrans (cell_congr (fst_pair _ _) (.eqRefl _)
    (Foundations.RuntimeAdjacentPermutationSwap.digit_congr (snd_pair _ _).fstE
      (snd_pair _ _).sndE (.eqRefl _)))
theorem selected_canonical (A m w : PTm n) : Γ ⊢[PRAAx] canonical (selectedDet A m w) :=
  GaussianScalarDeterminant.scalar_det_canonical _ _

/-- The permutation premise of the earlier retained sign endpoint is
unnecessary here: actual unequal adjacent digits suffice for actual parity. -/
theorem sign_flip_distinct (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hne : Γ ⊢[PRAAx] neg (Foundations.RuntimePermutationWords.digit m w j ≐ Foundations.RuntimePermutationWords.digit m w (succ j))) : Γ ⊢[PRAAx]
    signPoint m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) ≐ qnegative (signPoint m w) := by
  have hp := Foundations.RuntimeAdjacentPermutationSwap.parity_flip m w j hj hne
  refine .orE (Foundations.RuntimePermutationWords.parity_cases m w) ?_ ?_
  · have hn := hp.wk.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))
    exact (sign_odd _ _ hn).eqTrans (negative_congr (sign_even _ _ Prf.hyp0)).eqSymm
  · have hn := hp.wk.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))
    exact (sign_even _ _ hn).eqTrans
      ((GaussianDeterminantSignTransport.negative_involution qone qone_canonical).eqSymm.eqTrans
        (negative_congr (sign_odd _ _ Prf.hyp0)).eqSymm)
theorem negative_both_product (u v : PTm n) : Γ ⊢[PRAAx] qmul (qnegative u) (qnegative v) ≐ qmul u v :=
  (negative_product _ _).eqSymm.eqTrans
    ((negative_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (negative_product _ _).eqSymm)).eqTrans
        ((GaussianDeterminantSignTransport.negative_involution _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
          (GaussianRationalPowerAlgebra.qmul_commutative _ _)))
theorem sign_square (m w : PTm n) : Γ ⊢[PRAAx] qmul (signPoint m w) (signPoint m w) ≐ qone := by
  refine .orE (Foundations.RuntimePermutationWords.parity_cases m w) ?_ ?_
  · exact (qmul_congr (sign_even _ _ Prf.hyp0) (sign_even _ _ Prf.hyp0)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ qone_canonical)
  · exact (qmul_congr (sign_odd _ _ Prf.hyp0) (sign_odd _ _ Prf.hyp0)).eqTrans
      ((negative_both_product _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ qone_canonical))
theorem sign_unscale (m w z : PTm n) (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx]
    qmul (signPoint m w) (qmul (signPoint m w) z) ≐ z :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (sign_square _ _) (.eqRefl _)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical _ hz))

/-- Genuine characteristic-two exclusion via native positive integer cancellation. -/
theorem native_coordinate_zero (u : ZT n) (h : Γ ⊢[PRAAx] ZT.eq u (-u)) : Γ ⊢[PRAAx] ZT.eq u (ZT.natLit 0) := by
  apply RationalNormalForm.positive_integer_cancel two _ _ (zero_lt_succ one)
  ipra_lc ZT.toZ_eq h

theorem native_no_two_torsion (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (h : Γ ⊢[PRAAx] q ≐ qnegative q) : Γ ⊢[PRAAx] q ≐ qzero := by
  have native := GaussianReciprocalHorner.numerator_unique q (rawGaussian q) (ComplexLogarithmRemainder.neg (rawGaussian q)) (rawDen q)
    (raw_represents q)
    (represents_congr h.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
      (qnegative_represents _ _ _ (raw_represents q)))
  have hr : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (rawGaussian q)) (-ComplexLogarithmRemainder.re (rawGaussian q)) := by
    apply ZT.derive
    have e := GaussianRootAlgebra.equal_re native
    simpa only [GaussianRootAlgebra.re_neg,ZT.toZ_neg] using e
  have hi : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.im (rawGaussian q)) (-ComplexLogarithmRemainder.im (rawGaussian q)) := by
    apply ZT.derive
    have e := GaussianRootAlgebra.equal_im native
    simpa only [GaussianRootAlgebra.im_neg,ZT.toZ_neg] using e
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (rawGaussian q) ComplexLogarithmRemainder.zeroCode := by
    apply GaussianRootAlgebra.equal_of_values
    · simpa only [ZT.toZ_natLit,GaussianRootAlgebra.re_zero,Nat.cast_zero] using ZT.toZ_eq (native_coordinate_zero _ hr)
    · simpa only [ZT.toZ_natLit,GaussianRootAlgebra.im_zero,Nat.cast_zero] using ZT.toZ_eq (native_coordinate_zero _ hi)
  exact canonical_unique _ _ _ _ hq qzero_canonical (raw_den_positive q)
    (represents_congr (.eqRefl _) eq (.eqRefl _) (raw_represents q)) (GaussianRationalHorner.zero_represents _)

/-- Only the original numeric adjacent guard is needed for the actual
column-position composition; no permutation or word-horizon premise. -/
theorem selection_swap_cell (A m w j r i : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    evaluate (cell (GaussianScalarDeterminant.constantTable (columns A m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j)) m) r i) qzero ≐
      evaluate (cell (GaussianPolynomialColumnAlternation.CS (GaussianScalarDeterminant.constantTable (columns A m w) m) m j) r i) qzero := by
  have ht := Foundations.RuntimeAdjacentPermutationSwap.tau_range m j i hj hi
  have lhs := (GaussianScalarDeterminant.constant_cell_evaluation (columns A m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j)) m r i qzero hr hi).eqTrans
    ((recode_congr (columns_lookup A m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) r i hr hi)).eqTrans
      (recode_congr (cell_congr (.eqRefl A) (.eqRefl r) (Foundations.RuntimeAdjacentPermutationSwap.swapped_digit m w j i hj hi))))
  have rhs := (GaussianRationalMonicReduction.evaluate_congr
    (GaussianPolynomialColumnAlternation.cell_active (GaussianScalarDeterminant.constantTable (columns A m w) m) m j r i hr hi hj) (.eqRefl qzero)).eqTrans
      ((GaussianScalarDeterminant.constant_cell_evaluation (columns A m w) m r (Foundations.RuntimeAdjacentPermutationSwap.tau j i) qzero hr ht).eqTrans
        (recode_congr (columns_lookup A m w r (Foundations.RuntimeAdjacentPermutationSwap.tau j i) hr ht)))
  exact lhs.eqTrans rhs.eqSymm

theorem selection_swap_values (A m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.cellValuesEqual
      (GaussianScalarDeterminant.constantTable (columns A m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j)) m)
      (GaussianPolynomialColumnAlternation.CS (GaussianScalarDeterminant.constantTable (columns A m w) m) m j) m qzero qzero := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
  have js : Δ ⊢[PRAAx] lt (succ (Syn.shift (Syn.shift j))) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift.shift.wk.wk
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_columns,
    GaussianScalarDeterminant.subst_constantTable,Foundations.RuntimeAdjacentPermutationSwap.subst_swapWord,
    GaussianPolynomialColumnAlternation.subst_CS,GaussianRationalHorner.subst_qzero] using
    selection_swap_cell (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift j)) (var 1) (var 0) rr jj js

theorem selection_swap (A m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    selectedDet A m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) ≐ qnegative (selectedDet A m w) :=
  (GaussianScalarDeterminant.determinant_evaluation_congr _ _ _ zero zero qzero qzero
    (GaussianScalarDeterminant.constant_shape _ _) (GaussianPolynomialColumnAlternation.CS_shape _ _ _ _ (GaussianScalarDeterminant.constant_shape _ _))
    (selection_swap_values _ _ _ _ hj)).eqTrans
      (GaussianPolynomialColumnAlternation.column_evaluation_neg _ _ _ _ _ (GaussianScalarDeterminant.constant_shape _ _) hj)

def adjacentColumnsEqual (A m j : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ GaussianRationalValueEquality.valueEqual
    (cell (Syn.shift A) (var 0) (Syn.shift j)) (cell (Syn.shift A) (var 0) (succ (Syn.shift j))))
ipra_subst adjacentColumnsEqual [Syn.subst_shift, Syn.shift_subst]
theorem adjacent_columns_at (A m j r : PTm n) (h : Γ ⊢[PRAAx] adjacentColumnsEqual A m j)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] GaussianRationalValueEquality.valueEqual (cell A r j) (cell A r (succ j)) := by
  have rule := h.allE r
  simp only [adjacentColumnsEqual,Fm.subst_imp,subst_lt,GaussianRationalValueEquality.subst_valueEqual,
    GaussianPolynomialDeterminantTerms.subst_cell,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at rule
  exact .impE rule hr

theorem adjacent_tau_value (A m j r i : PTm n) (h : Γ ⊢[PRAAx] adjacentColumnsEqual A m j)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    recode (cell A r (Foundations.RuntimeAdjacentPermutationSwap.tau j i)) ≐ recode (cell A r i) := by
  have hv := (GaussianRationalValueEquality.recode_equal_iff _ _).iffMpr (adjacent_columns_at _ _ _ _ h hr)
  refine .orE (eq_or_ne i j) ?_ ?_
  · have ti : (i ≐ j) :: Γ ⊢[PRAAx] Foundations.RuntimeAdjacentPermutationSwap.tau j i ≐ succ j :=
      (Foundations.RuntimeAdjacentPermutationSwap.tau_congr (.eqRefl j) Prf.hyp0).eqTrans
        (Foundations.RuntimeAdjacentPermutationSwap.tau_left j)
    exact (recode_congr (cell_congr (.eqRefl _) (.eqRefl _) ti)).eqTrans
      (hv.wk.eqSymm.eqTrans (recode_congr (cell_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm)))
  · refine .orE (eq_or_ne i (succ j)) ?_ ?_
    · have ti : (i ≐ succ j) :: neg (i ≐ j) :: Γ ⊢[PRAAx] Foundations.RuntimeAdjacentPermutationSwap.tau j i ≐ j :=
        (Foundations.RuntimeAdjacentPermutationSwap.tau_congr (.eqRefl j) Prf.hyp0).eqTrans
          (Foundations.RuntimeAdjacentPermutationSwap.tau_right j)
      exact (recode_congr (cell_congr (.eqRefl _) (.eqRefl _) ti)).eqTrans
        (hv.wk.wk.eqTrans (recode_congr (cell_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm)))
    · exact recode_congr (cell_congr (.eqRefl _) (.eqRefl _)
        (Foundations.RuntimeAdjacentPermutationSwap.tau_other j i Prf.hyp1 Prf.hyp0))

theorem equal_columns_cell (A m j r i : PTm n) (h : Γ ⊢[PRAAx] adjacentColumnsEqual A m j)
    (hr : Γ ⊢[PRAAx] lt r m) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    evaluate (cell (GaussianPolynomialColumnAlternation.CS (GaussianScalarDeterminant.constantTable A m) m j) r i) qzero ≐
      evaluate (cell (GaussianScalarDeterminant.constantTable A m) r i) qzero :=
  (GaussianRationalMonicReduction.evaluate_congr (GaussianPolynomialColumnAlternation.cell_active _ _ _ _ _ hr hi hj) (.eqRefl _)).eqTrans
    ((GaussianScalarDeterminant.constant_cell_evaluation _ _ _ _ _ hr (Foundations.RuntimeAdjacentPermutationSwap.tau_range _ _ _ hj hi)).eqTrans
      ((adjacent_tau_value _ _ _ _ _ h hr).eqTrans (GaussianScalarDeterminant.constant_cell_evaluation _ _ _ _ _ hr hi).eqSymm))

theorem equal_columns_values (A m j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (h : Γ ⊢[PRAAx] adjacentColumnsEqual A m j) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.cellValuesEqual (GaussianPolynomialColumnAlternation.CS (GaussianScalarDeterminant.constantTable A m) m j)
      (GaussianScalarDeterminant.constantTable A m) m qzero qzero := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
  have js : Δ ⊢[PRAAx] lt (succ (Syn.shift (Syn.shift j))) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift.shift.wk.wk
  have hs : Δ ⊢[PRAAx] adjacentColumnsEqual (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_adjacentColumnsEqual,Syn.shift] using h.shift.shift.wk.wk
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,GaussianScalarDeterminant.subst_constantTable,
    GaussianPolynomialColumnAlternation.subst_CS,GaussianRationalHorner.subst_qzero] using
    equal_columns_cell (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j)) (var 1) (var 0) hs rr jj js

theorem adjacent_equal_columns_zero (A m j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (h : Γ ⊢[PRAAx] adjacentColumnsEqual A m j) : Γ ⊢[PRAAx] GaussianScalarDeterminant.scalarDet A m ≐ qzero := by
  have e := GaussianScalarDeterminant.determinant_evaluation_congr _ _ m zero zero qzero qzero
    (GaussianPolynomialColumnAlternation.CS_shape _ _ _ _ (GaussianScalarDeterminant.constant_shape _ _))
    (GaussianScalarDeterminant.constant_shape _ _) (equal_columns_values _ _ _ hj h)
  exact native_no_two_torsion _ (GaussianScalarDeterminant.scalar_det_canonical _ _)
    (e.eqSymm.eqTrans (GaussianPolynomialColumnAlternation.column_evaluation_neg _ _ _ _ _ (GaussianScalarDeterminant.constant_shape _ _) hj))

theorem selection_tie_columns (A m w j : PTm n) (h : Γ ⊢[PRAAx] Foundations.RuntimeWordSorting.adjacentTie m w j) : Γ ⊢[PRAAx]
    adjacentColumnsEqual (columns A m w) m j := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] Foundations.RuntimeWordSorting.adjacentTie (Syn.shift m) (Syn.shift w) (Syn.shift j) := by
    simpa only [Δ,Fm.shift,Foundations.RuntimeWordSorting.subst_adjacentTie,Syn.shift] using h.shift.wk
  have j1 := Prf.andE₁ hs
  have j0 := lt_of_le_of_lt (le_succ_self _) j1
  have e := (columns_lookup (Syn.shift A) (Syn.shift m) (Syn.shift w) (var 0) (Syn.shift j) Prf.hyp0 j0).eqTrans
    ((cell_congr (.eqRefl _) (.eqRefl _) (.andE₂ hs)).eqTrans
      (columns_lookup (Syn.shift A) (Syn.shift m) (Syn.shift w) (var 0) (succ (Syn.shift j)) Prf.hyp0 j1).eqSymm)
  simpa only [Δ,Syn.shift,subst_columns,ConciseIPRA.PTm.subst_succ] using GaussianRationalValueEquality.value_equal_of_code e

theorem selection_adjacent_tie_zero (A m w j : PTm n) (h : Γ ⊢[PRAAx] Foundations.RuntimeWordSorting.adjacentTie m w j) : Γ ⊢[PRAAx]
    selectedDet A m w ≐ qzero := adjacent_equal_columns_zero _ _ _ (.andE₁ h) (selection_tie_columns _ _ _ _ h)

/-- Identity bits are zero ONLY on the actual bounded column cut. The
inversion checker itself has no implicit j<m guard. -/
theorem identity_inversion_bit (m i j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.inversionBit m (Foundations.RuntimeWordSorting.identityCode m) i j ≐ zero := by
  refine .orE (Foundations.RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0 ?_
  have pair : (Foundations.RuntimePermutationWords.inversionBit m (Foundations.RuntimeWordSorting.identityCode m) i j ≐ one) :: Γ ⊢[PRAAx]
      lt i j ⋏ lt (Foundations.RuntimePermutationWords.digit m (Foundations.RuntimeWordSorting.identityCode m) j)
        (Foundations.RuntimePermutationWords.digit m (Foundations.RuntimeWordSorting.identityCode m) i) :=
    (Foundations.RuntimePermutationWords.inversion_reflection m (Foundations.RuntimeWordSorting.identityCode m) i j).iffMp Prf.hyp0
  have hi := lt_of_le_of_lt (le_of_lt (.andE₁ pair)) hj.wk
  have reverse := lt_congr (Foundations.RuntimeWordSorting.identity_code_digit _ _ hj.wk)
    (Foundations.RuntimeWordSorting.identity_code_digit _ _ hi) (.andE₂ pair)
  exact lt_irrefl _ _ (lt_of_lt_of_le reverse (le_of_lt (.andE₁ pair)))

theorem identity_row_zero (m i t : PTm n) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.rowPrefix m (Foundations.RuntimeWordSorting.identityCode m) i t ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift m) ⟶
      Foundations.RuntimePermutationWords.rowPrefix (Syn.shift m) (Foundations.RuntimeWordSorting.identityCode (Syn.shift m)) (Syn.shift i) (var 0) ≐ zero) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, Foundations.RuntimePermutationWords.subst_rowPrefix,
        Foundations.RuntimeWordSorting.subst_identityCode]
    · exact .impI (Foundations.RuntimePermutationWords.row_zero _ _ _)
    · refine .impI ?_
      exact (Foundations.RuntimePermutationWords.row_succ _ _ _ _).eqTrans
        ((congrAdd (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)) (identity_inversion_bit _ _ _ Prf.hyp0)).eqTrans (add_zero _))
  have rule : Γ ⊢[PRAAx] le t m ⟶ Foundations.RuntimePermutationWords.rowPrefix m (Foundations.RuntimeWordSorting.identityCode m) i t ≐ zero := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,Foundations.RuntimePermutationWords.subst_rowPrefix,
      Foundations.RuntimeWordSorting.subst_identityCode,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE rule ht

theorem identity_prefix_zero (m t : PTm n) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.inversionPrefix m (Foundations.RuntimeWordSorting.identityCode m) t ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (Foundations.RuntimePermutationWords.inversionPrefix (Syn.shift m)
      (Foundations.RuntimeWordSorting.identityCode (Syn.shift m)) (var 0) ≐ zero) := by
    ipra_qfind [Foundations.RuntimePermutationWords.subst_inversionPrefix,
        Foundations.RuntimeWordSorting.subst_identityCode]
    · exact Foundations.RuntimePermutationWords.inversion_prefix_zero _ _
    · exact (Foundations.RuntimePermutationWords.inversion_prefix_succ _ _ _).eqTrans
        ((congrAdd Prf.hyp0 (identity_row_zero _ _ _ (le_refl _))).eqTrans (add_zero _))
  simpa only [Fm.subst_eq,Foundations.RuntimePermutationWords.subst_inversionPrefix,Foundations.RuntimeWordSorting.subst_identityCode,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem sign_identity (m : PTm n) : Γ ⊢[PRAAx] signPoint m (Foundations.RuntimeWordSorting.identityCode m) ≐ qone :=
  sign_even _ _ ((congrAp1 parF (identity_prefix_zero _ _)).eqTrans par_zero)

theorem columns_identity_values (A m : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarCellsEqual (columns A m (Foundations.RuntimeWordSorting.identityCode m)) A m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
  have e := (columns_lookup (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m))
    (Foundations.RuntimeWordSorting.identityCode (Syn.shift (Syn.shift m))) (var 1) (var 0) rr jj).eqTrans
      (cell_congr (.eqRefl _) (.eqRefl _) (Foundations.RuntimeWordSorting.identity_code_digit _ _ jj))
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_columns,Foundations.RuntimeWordSorting.subst_identityCode] using
    GaussianRationalValueEquality.value_equal_of_code e

theorem columns_identity_det (A m : PTm n) : Γ ⊢[PRAAx]
    selectedDet A m (Foundations.RuntimeWordSorting.identityCode m) ≐ GaussianScalarDeterminant.scalarDet A m :=
  GaussianScalarDeterminant.scalar_det_congr _ _ _ (columns_identity_values _ _)
theorem signed_identity (A m : PTm n) : Γ ⊢[PRAAx]
    signedSelection A m (Foundations.RuntimeWordSorting.identityCode m) ≐ GaussianScalarDeterminant.scalarDet A m :=
  (qmul_congr (sign_identity _) (columns_identity_det _ _)).eqTrans
    (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianScalarDeterminant.scalar_det_canonical _ _))

/-- Both signs really flip at an active step. No horizon, permutation or
nonzero scalar guard is needed for this one-step equation. -/
theorem step_signed_selection (A m w : PTm n) : Γ ⊢[PRAAx]
    signedSelection A m (Foundations.RuntimeWordSorting.sortStep m w) ≐ signedSelection A m w := by
  refine .orE (Foundations.RuntimeWordSorting.active_cases m w) ?_ ?_
  · exact signed_selection_congr (.eqRefl _) (.eqRefl _)
      (Foundations.RuntimeWordSorting.step_inactive _ _ (Foundations.RuntimeWordSorting.inactive_of_active_zero _ _ Prf.hyp0))
  · have found := Foundations.RuntimeWordSorting.descent_found m w (Prf.hyp0 (Γ := Γ))
    have hj := Prf.andE₁ found
    have hne := Foundations.RuntimeAdjacentPermutationSwap.different_symm
      (Foundations.RuntimeAdjacentPermutationSwap.different_of_lt (Prf.andE₂ found))
    exact (signed_selection_congr (.eqRefl A) (.eqRefl m) (Foundations.RuntimeWordSorting.step_active _ _ Prf.hyp0)).eqTrans
      ((qmul_congr (sign_flip_distinct _ _ _ hj hne) (selection_swap _ _ _ _ hj)).eqTrans (negative_both_product _ _))

/-- A genuine QF induction over the SAME numerical sorting state. The
original horizon is required only when interpreting its final branch. -/
theorem trajectory_invariant (A m w t : PTm n) : Γ ⊢[PRAAx]
    signedSelection A m (Foundations.RuntimeWordSorting.state m w t) ≐ signedSelection A m w := by
  have all : Γ ⊢[PRAAx] .all
      (signedSelection (Syn.shift A) (Syn.shift m) (Foundations.RuntimeWordSorting.state (Syn.shift m) (Syn.shift w) (var 0)) ≐
        signedSelection (Syn.shift A) (Syn.shift m) (Syn.shift w)) := by
    ipra_qfind [subst_signedSelection, Foundations.RuntimeWordSorting.subst_state]
    · exact signed_selection_congr (.eqRefl _) (.eqRefl _) (Foundations.RuntimeWordSorting.state_zero _ _)
    · exact (signed_selection_congr (.eqRefl _) (.eqRefl _) (Foundations.RuntimeWordSorting.state_succ _ _ _)).eqTrans
        ((step_signed_selection _ _ _).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,subst_signedSelection,Foundations.RuntimeWordSorting.subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem selection_permutation (A m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ one) : Γ ⊢[PRAAx]
    selectedDet A m w ≐ qmul (signPoint m w) (GaussianScalarDeterminant.scalarDet A m) := by
  have endValue : Γ ⊢[PRAAx] signedSelection A m (Foundations.RuntimeWordSorting.final m w) ≐ GaussianScalarDeterminant.scalarDet A m :=
    (signed_selection_congr (.eqRefl _) (.eqRefl _) (Foundations.RuntimeWordSorting.permutation_final_identity _ _ hw hp)).eqTrans (signed_identity _ _)
  have equation := (trajectory_invariant A m w (Foundations.RuntimeWordSorting.fuel m)).eqSymm.eqTrans endValue
  exact (sign_unscale _ _ _ (selected_canonical _ _ _)).eqSymm.eqTrans
    (qmul_congr (.eqRefl _) equation)

theorem selection_nonpermutation (A m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ zero) : Γ ⊢[PRAAx] selectedDet A m w ≐ qzero := by
  have hz := selection_adjacent_tie_zero A m (Foundations.RuntimeWordSorting.final m w)
    (Foundations.RuntimeWordSorting.tieIndex m (Foundations.RuntimeWordSorting.final m w))
    (Foundations.RuntimeWordSorting.nonpermutation_final_tie _ _ hw hp)
  have endValue : Γ ⊢[PRAAx] signedSelection A m (Foundations.RuntimeWordSorting.final m w) ≐ qzero :=
    (qmul_congr (.eqRefl _) hz).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
  have equation := (trajectory_invariant A m w (Foundations.RuntimeWordSorting.fuel m)).eqSymm.eqTrans endValue
  exact (sign_unscale _ _ _ (selected_canonical _ _ _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) equation).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem selection_normal_form (A m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m)) : Γ ⊢[PRAAx]
    selectedDet A m w ≐ expected A m w := by
  refine .orE (Foundations.RuntimePermutationWords.checker_cases m w) ?_ ?_
  · exact (selection_nonpermutation _ _ _ hw.wk Prf.hyp0).eqTrans (Foundations.GuardedTotalization.sel_zero Prf.hyp0).eqSymm
  · exact (selection_permutation _ _ _ hw.wk Prf.hyp0).eqTrans (Foundations.GuardedTotalization.sel_one Prf.hyp0).eqSymm

theorem empty_selection (A w : PTm n) : Γ ⊢[PRAAx] selectedDet A zero w ≐ qone :=
  GaussianPolynomialDeterminant.empty_evaluation _ _ _

/-- Seven actual fields retain the original scalar determinant and the
SAME sorting payload; no witness is extracted from a correctness proof. -/
def output (A m w : PTm n) : PTm n := pairT (columns A m w)
  (pairT (selectedDet A m w) (pairT (GaussianScalarDeterminant.scalarDet A m)
    (pairT (signPoint m w) (pairT (Foundations.RuntimePermutationWords.permutationBit m w)
      (pairT (Foundations.RuntimeWordSorting.run m w) (expected A m w))))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (A m w : PTm n) : PTm n := ap3 outputF A m w
ipra_subst output
ipra_subst run
theorem program_at (A m w : PTm n) : Γ ⊢[PRAAx] run A m w ≐ output A m w := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2)) ![A,m,w]
theorem returned_columns (A m w : PTm n) : Γ ⊢[PRAAx] fstT (run A m w) ≐ columns A m w :=
  (program_at _ _ _).fstE
theorem returned_selection (A m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A m w)) ≐ selectedDet A m w :=
  (program_at _ _ _).sndE.fstE
theorem returned_original (A m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A m w))) ≐ GaussianScalarDeterminant.scalarDet A m :=
  (program_at _ _ _).sndE.sndE.fstE
theorem returned_sign (A m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run A m w)))) ≐ signPoint m w :=
  (program_at _ _ _).sndE.sndE.sndE.fstE
theorem returned_checker (A m w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run A m w))))) ≐ Foundations.RuntimePermutationWords.permutationBit m w :=
  (program_at _ _ _).sndE.sndE.sndE.sndE.fstE
theorem returned_sorting (A m w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (sndT (run A m w)))))) ≐ Foundations.RuntimeWordSorting.run m w :=
  (program_at _ _ _).sndE.sndE.sndE.sndE.sndE.fstE
theorem returned_expected (A m w : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (sndT (run A m w)))))) ≐ expected A m w :=
  (program_at _ _ _).sndE.sndE.sndE.sndE.sndE.sndE
theorem returned_normal_form (A m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m)) : Γ ⊢[PRAAx]
    fstT (sndT (run A m w)) ≐ sndT (sndT (sndT (sndT (sndT (sndT (run A m w)))))) :=
  (returned_selection _ _ _).eqTrans ((selection_normal_form _ _ _ hw).eqTrans (returned_expected _ _ _).eqSymm)
theorem returned_selection_canonical (A m w : PTm n) : Γ ⊢[PRAAx] canonical (fstT (sndT (run A m w))) :=
  GaussianRationalHorner.canonical_congr (returned_selection _ _ _) (selected_canonical _ _ _)

/-! Every table, dimension, original word, swap/row/column index and
trajectory length remains numerically quantified in ordinary PRA. -/
theorem actual_selected_table_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 1) ⟶
      cell (columns (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
        cell (var 0) (var 3) (Foundations.RuntimePermutationWords.digit (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (columns_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_distinct_sign_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 2)) (var 0) ⟶
      neg (Foundations.RuntimePermutationWords.digit (var 0) (var 1) (var 2) ≐
        Foundations.RuntimePermutationWords.digit (var 0) (var 1) (succ (var 2))) ⟶
      signPoint (var 0) (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 0) (var 1) (var 2)) ≐ qnegative (signPoint (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (sign_flip_distinct _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_sign_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qmul (signPoint (var 0) (var 1)) (signPoint (var 0) (var 1)) ≐ qone) := closeUniv 2 (sign_square _ _)
theorem canonical_no_two_torsion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (canonical (var 0) ⟶ var 0 ≐ qnegative (var 0) ⟶ var 0 ≐ qzero) :=
  closeUniv 1 (.impI (.impI (native_no_two_torsion _ Prf.hyp1 Prf.hyp0)))
theorem actual_selected_swap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (succ (var 3)) (var 1) ⟶ selectedDet (var 0) (var 1) (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 1) (var 2) (var 3)) ≐
      qnegative (selectedDet (var 0) (var 1) (var 2))) := closeUniv 4 (.impI (selection_swap _ _ _ _ Prf.hyp0))
theorem actual_equal_columns_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 2)) (var 1) ⟶ adjacentColumnsEqual (var 0) (var 1) (var 2) ⟶
      GaussianScalarDeterminant.scalarDet (var 0) (var 1) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (adjacent_equal_columns_zero _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_selected_tie_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Foundations.RuntimeWordSorting.adjacentTie (var 1) (var 2) (var 3) ⟶ selectedDet (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 4 (.impI (selection_adjacent_tie_zero _ _ _ _ Prf.hyp0))
theorem actual_identity_selection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (selectedDet (var 0) (var 1) (Foundations.RuntimeWordSorting.identityCode (var 1)) ≐ GaussianScalarDeterminant.scalarDet (var 0) (var 1)) :=
  closeUniv 2 (columns_identity_det _ _)
theorem actual_sort_signed_invariant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (signedSelection (var 0) (var 1) (Foundations.RuntimeWordSorting.state (var 1) (var 2) (var 3)) ≐ signedSelection (var 0) (var 1) (var 2)) :=
  closeUniv 4 (trajectory_invariant _ _ _ _)
theorem actual_selection_permutation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶ Foundations.RuntimePermutationWords.permutationBit (var 1) (var 2) ≐ one ⟶
      selectedDet (var 0) (var 1) (var 2) ≐ qmul (signPoint (var 1) (var 2)) (GaussianScalarDeterminant.scalarDet (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (selection_permutation _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_selection_nonpermutation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶ Foundations.RuntimePermutationWords.permutationBit (var 1) (var 2) ≐ zero ⟶
      selectedDet (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (selection_nonpermutation _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_selection_normal_form_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶ selectedDet (var 0) (var 1) (var 2) ≐ expected (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (selection_normal_form _ _ _ Prf.hyp0))
theorem actual_empty_selection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (selectedDet (var 0) zero (var 1) ≐ qone) := closeUniv 2 (empty_selection _ _)
theorem actual_selection_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_normal_form_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2))) ≐ sndT (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))))) :=
  closeUniv 3 (.impI (returned_normal_form _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianScalarColumnSelection
