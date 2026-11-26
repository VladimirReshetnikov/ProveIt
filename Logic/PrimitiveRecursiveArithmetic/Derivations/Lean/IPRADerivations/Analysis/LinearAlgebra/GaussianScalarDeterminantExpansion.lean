import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDeterminant
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTupleExpansion
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalProductAlgebra

/-!
# Expansion of the actual scalar determinant of a matrix product

For each word used by the determinant, expand the product of the selected
dot sums by the actual mixed-radix tuple fold. The dot count, dimension,
input matrix codes and word are all numerical object terms.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantExpansion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell signPoint)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (termsEqual)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm


variable {n : ℕ} {Γ : List (Fm PTm n)}

open GaussianRationalMatrixFiniteSums (scalarData scalarFields subst_scalarData subst_scalarFields scalar_fields_at matrixProduct subst_matrixProduct)
open GaussianRationalTupleExpansion (tupleBody tupleData tupleSum choiceBody choiceData choiceProduct subst_choiceProduct tuple_body_at)

/-- At column `j` and dot index `k`, read `A[w_j,k]`. -/
def leftEntry : PTm 3 :=
  let x := var 2
  let r := Foundations.RuntimePermutationWords.digit (scalarFields x 2) (scalarFields x 3) (var 0)
  cell (scalarFields x 0) r (var 1)

/-- At column `j` and dot index `k`, read `B[k,j]`. -/
def rightEntry : PTm 3 := cell (scalarFields (var 2) 1) (var 1) (var 0)

def dotEntry : PTm 3 := qmul leftEntry rightEntry

theorem left_entry_at (A B m w j k : PTm n) : Γ ⊢[PRAAx]
    inst3 leftEntry j k (scalarData A B m w) ≐ cell A (Foundations.RuntimePermutationWords.digit m w j) k := by
  simp only [leftEntry,inst3,GaussianPolynomialDeterminantTerms.subst_cell,
    Foundations.RuntimePermutationWords.subst_digit,subst_scalarFields,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact entry_congr (entry_congr (scalar_fields_at A B m w 0)
    (Foundations.RuntimeAdjacentPermutationSwap.digit_congr (scalar_fields_at A B m w 2)
      (scalar_fields_at A B m w 3) (.eqRefl _))) (.eqRefl _)

theorem right_entry_at (A B m w j k : PTm n) : Γ ⊢[PRAAx]
    inst3 rightEntry j k (scalarData A B m w) ≐ cell B k j := by
  simp only [rightEntry,inst3,GaussianPolynomialDeterminantTerms.subst_cell,
    subst_scalarFields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact entry_congr (entry_congr (scalar_fields_at A B m w 1) (.eqRefl _)) (.eqRefl _)

theorem dot_entry_at (A B m w j k : PTm n) : Γ ⊢[PRAAx]
    inst3 dotEntry j k (scalarData A B m w) ≐
      qmul (cell A (Foundations.RuntimePermutationWords.digit m w j) k) (cell B k j) := by
  simpa only [dotEntry,inst3,GaussianRationalHorner.subst_qmul] using
    qmul_congr (left_entry_at (Γ := Γ) A B m w j k) (right_entry_at A B m w j k)

/-- The two products are computed independently from the original digit choices. -/
theorem choice_product_split (m d u x : PTm n) : Γ ⊢[PRAAx]
    choiceProduct dotEntry m d u x ≐ qmul (choiceProduct leftEntry m d u x) (choiceProduct rightEntry m d u x) := by
  have bodies : choiceBody dotEntry = GaussianRationalProductAlgebra.multiplyBody (choiceBody leftEntry) (choiceBody rightEntry) := by
    simp only [dotEntry,choiceBody,GaussianRationalProductAlgebra.multiplyBody,inst3,GaussianRationalHorner.subst_qmul]
  simpa only [choiceProduct,bodies] using
    GaussianRationalProductAlgebra.product_multiply (Γ := Γ) (choiceBody leftEntry) (choiceBody rightEntry) d (choiceData m u x)

theorem row_at (A B m w j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row dotEntry j m (GaussianRationalMatrixFiniteSums.scalarData A B m w) ≐ GaussianRationalMatrixFiniteSums.scalarDot A B m (Foundations.RuntimePermutationWords.digit m w j) j := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalFubini.row,GaussianRationalMatrixFiniteSums.subst_scalarData,Foundations.RuntimePermutationWords.subst_digit,subst_pairT] using
    (GaussianRationalFubini.row_entry dotEntry (Syn.shift j) (var 0)
      (GaussianRationalMatrixFiniteSums.scalarData (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift w))).eqTrans
      ((dot_entry_at (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift w) (Syn.shift j) (var 0)).eqTrans
        (GaussianRationalMatrixFiniteSums.scalar_body_at (Syn.shift A) (Syn.shift B) (Foundations.RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (Syn.shift j))
          (Syn.shift j) (var 0)).eqSymm)

theorem product_word_expansion (A B m w : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.rawProduct (GaussianRationalMatrixFiniteSums.matrixProduct A B m) m w ≐ GaussianRationalTupleExpansion.tupleSum dotEntry m m (GaussianRationalMatrixFiniteSums.scalarData A B m w) := by
  have h : Γ ⊢[PRAAx] termsEqual GaussianScalarDeterminant.factorBody (GaussianRationalFubini.rowSumBody dotEntry) m
      (GaussianScalarDeterminant.factorData (GaussianRationalMatrixFiniteSums.matrixProduct A B m) m w) (pairT m (GaussianRationalMatrixFiniteSums.scalarData A B m w)) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let m' := Syn.shift m
    let w' := Syn.shift w
    have hj : lt (var 0) m' :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) m' := Prf.hyp0
    have hr := Foundations.RuntimePermutationWords.digit_bound m' w' (var 0) hj
    have e := (GaussianScalarDeterminant.factor_body_at (GaussianRationalMatrixFiniteSums.matrixProduct A' B' m') m' w' (var 0)).eqTrans
      ((GaussianRationalMatrixFiniteSums.product_lookup A' B' m' (Foundations.RuntimePermutationWords.digit m' w' (var 0)) (var 0) hr hj).eqTrans
        ((row_at A' B' m' w' (var 0)).eqSymm.eqTrans
          (GaussianRationalFubini.row_sum_at dotEntry (var 0) m' (GaussianRationalMatrixFiniteSums.scalarData A' B' m' w')).eqSymm))
    simpa only [A',B',m',w',Syn.shift,GaussianScalarDeterminant.subst_factorData,GaussianRationalMatrixFiniteSums.subst_matrixProduct,GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using e
  exact (GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ h).eqTrans (GaussianRationalTupleExpansion.full_expansion dotEntry m _)

theorem product_word_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianScalarDeterminant.rawProduct (GaussianRationalMatrixFiniteSums.matrixProduct (var 0) (var 1) (var 2)) (var 2) (var 3) ≐
      GaussianRationalTupleExpansion.tupleSum dotEntry (var 2) (var 2) (GaussianRationalMatrixFiniteSums.scalarData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (product_word_expansion _ _ _ _)

open GaussianPolynomialDeterminant (wordCode subst_wordCode)
open GaussianPolynomialDeterminantTerms (subst_signPoint)
open GaussianScalarDeterminant (scalarDet scalarSum signedBody signedTerm signed_body_at scalar_leibniz)
open GaussianRationalFiniteSum (sum_multiply multiplyBody multiply_body_at)
open GaussianRationalFubini (row rowFirst columnFirst rowBody rowSumBody row_entry row_sum_at)

/-- The retained-rank sign times the contribution of one arbitrary choice word. -/
def signedChoiceEntry : PTm 3 :=
  let x := var 2
  let m := scalarFields x 2
  let w := wordCode m (var 0)
  qmul (signPoint m w)
    (choiceProduct dotEntry m m (var 1)
      (scalarData (scalarFields x 0) (scalarFields x 1) m w))

theorem signed_choice_at (A B m t u : PTm n) : Γ ⊢[PRAAx]
    inst3 signedChoiceEntry t u (scalarData A B m m) ≐
      qmul (signPoint m (wordCode m t))
        (choiceProduct dotEntry m m u (scalarData A B m (wordCode m t))) := by
  let x := scalarData A B m m
  have hm : Γ ⊢[PRAAx] scalarFields x 2 ≐ m := scalar_fields_at A B m m 2
  have hw : Γ ⊢[PRAAx] wordCode (scalarFields x 2) t ≐ wordCode m t := by
    simpa only [inst2,subst_wordCode,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (congrInst2 (wordCode (var 0) (var 1)) hm (Prf.eqRefl (Γ := Γ) t))
  simp only [signedChoiceEntry,inst3,GaussianRationalHorner.subst_qmul,subst_signPoint,
    subst_choiceProduct,subst_scalarData,subst_wordCode,subst_scalarFields,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  refine qmul_congr ?_ (GaussianRationalTupleExpansion.choice_product_congr _ hm hm (.eqRefl _) ?_)
  · simpa only [x,inst2,subst_signPoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (congrInst2 (signPoint (var 0) (var 1)) hm hw)
  · exact congrPairT (scalar_fields_at _ _ _ _ 0)
      (congrPairT (scalar_fields_at _ _ _ _ 1) (congrPairT hm hw))

theorem signed_choice_row (A B m t : PTm n) : Γ ⊢[PRAAx]
    row signedChoiceEntry t (Foundations.RuntimePermutationWords.horizon m) (scalarData A B m m) ≐ signedTerm (matrixProduct A B m) m t := by
  let w := wordCode m t
  let sign := signPoint m w
  let x := scalarData A B m w
  have h : Γ ⊢[PRAAx] termsEqual (rowBody signedChoiceEntry) (multiplyBody (tupleBody dotEntry))
      (Foundations.RuntimePermutationWords.horizon m) (pairT t (scalarData A B m m)) (pairT sign (tupleData m m x)) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let m' := Syn.shift m
    let t' := Syn.shift t
    let w' := wordCode m' t'
    let x' := scalarData A' B' m' w'
    let sign' := signPoint m' w'
    let Δ := lt (var 0) (Foundations.RuntimePermutationWords.horizon m') :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (rowBody signedChoiceEntry) (var 0) (pairT t' (scalarData A' B' m' m')) ≐
        inst2 (multiplyBody (tupleBody dotEntry)) (var 0) (pairT sign' (tupleData m' m' x')) :=
      (row_entry _ _ _ _).eqTrans ((signed_choice_at A' B' m' t' (var 0)).eqTrans
        ((multiply_body_at (tupleBody dotEntry) sign' (var 0) (tupleData m' m' x')).eqTrans
          (qmul_congr (.eqRefl _) (tuple_body_at dotEntry m' m' x' (var 0)))).eqSymm)
    simpa only [Δ,A',B',m',t',w',x',sign',w,sign,x,Syn.shift,subst_pairT,subst_scalarData,
      GaussianRationalTupleExpansion.subst_tupleData,subst_wordCode,subst_signPoint,Foundations.RuntimePermutationWords.subst_horizon] using e
  have first := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ h
  have second := sum_multiply (Γ := Γ) (tupleBody dotEntry) sign (Foundations.RuntimePermutationWords.horizon m) (tupleData m m x)
  have third := qmul_congr (Prf.eqRefl (Γ := Γ) sign) (product_word_expansion (Γ := Γ) A B m w).eqSymm
  exact first.eqTrans (second.eqTrans third)

/-- Move the arbitrary-choice sum outside the original retained-rank sum. -/
theorem determinant_choice_sum (A B m : PTm n) : Γ ⊢[PRAAx]
    scalarDet (matrixProduct A B m) m ≐ columnFirst signedChoiceEntry (Foundations.RuntimePermutationWords.count m) (Foundations.RuntimePermutationWords.horizon m) (scalarData A B m m) := by
  have h : Γ ⊢[PRAAx] termsEqual signedBody (rowSumBody signedChoiceEntry)
      (Foundations.RuntimePermutationWords.count m) (pairT (matrixProduct A B m) m) (pairT (Foundations.RuntimePermutationWords.horizon m) (scalarData A B m m)) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let m' := Syn.shift m
    let Δ := lt (var 0) (Foundations.RuntimePermutationWords.count m') :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (rowSumBody signedChoiceEntry) (var 0)
        (pairT (Foundations.RuntimePermutationWords.horizon m') (scalarData A' B' m' m')) ≐ inst2 signedBody (var 0) (pairT (matrixProduct A' B' m') m') :=
      (row_sum_at _ _ _ _).eqTrans ((signed_choice_row A' B' m' (var 0)).eqTrans (signed_body_at _ _ _).eqSymm)
    simpa only [Δ,A',B',m',Syn.shift,subst_pairT,subst_matrixProduct,Foundations.RuntimePermutationWords.subst_horizon,subst_scalarData,
      Foundations.RuntimePermutationWords.subst_count] using e.eqSymm
  have first := scalar_leibniz (Γ := Γ) (matrixProduct A B m) m
  have second := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ h
  have third := GaussianRationalFubini.fubini (Γ := Γ) signedChoiceEntry
    (Foundations.RuntimePermutationWords.count m) (Foundations.RuntimePermutationWords.horizon m) (scalarData A B m m)
  exact first.eqTrans (second.eqTrans third)

theorem determinant_choice_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scalarDet (matrixProduct (var 0) (var 1) (var 2)) (var 2) ≐
      columnFirst signedChoiceEntry (Foundations.RuntimePermutationWords.count (var 2)) (Foundations.RuntimePermutationWords.horizon (var 2))
        (scalarData (var 0) (var 1) (var 2) (var 2))) :=
  closeUniv 3 (determinant_choice_sum _ _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantExpansion
