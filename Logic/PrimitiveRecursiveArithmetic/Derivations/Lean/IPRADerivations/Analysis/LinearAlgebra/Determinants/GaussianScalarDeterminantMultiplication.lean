import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminantExpansion
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarColumnSelection
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalBlockSums

/-!
# Multiplicativity of the actual scalar determinant

After expanding the determinant of the matrix product over all choice words,
each inner sum is a determinant of selected columns of the left matrix
times the corresponding word product of the right matrix. Sorting proves
that a repeated digit gives zero and that a permutation contributes its
sign times the original determinant. The existing filter then recovers the
determinant of the right matrix.

Both inputs may be arbitrary scalar table codes. Every size, word and index
in this proof is numerical, and the closed theorem has no premises.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantMultiplication

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell signPoint subst_signPoint)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant (wordCode subst_wordCode)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant
  (scalarDet scalarSum signedBody signedTerm signed_body_at scalar_leibniz rawProduct
    subst_rawProduct subst_factorData factor_body_at)
open LeanProofs.IPRA.Analysis.GaussianScalarColumnSelection (columns subst_columns columns_lookup selectedDet)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminantExpansion
  (leftEntry rightEntry signedChoiceEntry left_entry_at right_entry_at signed_choice_at choice_product_split)
open LeanProofs.IPRA.Analysis.GaussianRationalTupleExpansion
  (choiceProduct subst_choiceData choice_body_at)
open LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums (scalarData subst_scalarData matrixProduct)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (qmul_associative)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra (qmul_commutative)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (termsEqual multiplyBody multiply_body_at sum_multiply)
open LeanProofs.IPRA.Analysis.GaussianRationalFubini (column columnBody column_entry)

local notation "wordLimit" => Foundations.RuntimePermutationWords.horizon
local notation "retainedCount" => Foundations.RuntimePermutationWords.count
local notation "wordFilter" => Foundations.RuntimePermutationWords.keepBody
local notation "wordBit" => Foundations.RuntimePermutationWords.permutationBit

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The left factors read the selected columns of the original left matrix. -/
theorem left_choice (A B m w u : PTm n) : Γ ⊢[PRAAx]
    choiceProduct leftEntry m m u (scalarData A B m w) ≐ rawProduct (columns A m u) m w := by
  apply GaussianRationalFiniteProduct.product_congr_bounded
  refine .allI (.impI ?_)
  let A' := Syn.shift A
  let B' := Syn.shift B
  let m' := Syn.shift m
  let w' := Syn.shift w
  let u' := Syn.shift u
  let j : PTm (n + 1) := var 0
  let Δ := lt j m' :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt j m' := Prf.hyp0
  have hr := Foundations.RuntimePermutationWords.digit_bound m' w' j hj
  have first := choice_body_at (Γ := Δ) leftEntry m' u' (scalarData A' B' m' w') j
  have second := left_entry_at (Γ := Δ) A' B' m' w' j (Foundations.RuntimePermutationWords.digit m' u' j)
  have selectedFactor := factor_body_at (Γ := Δ) (columns A' m' u') m' w' j
  have originalCell := columns_lookup (Γ := Δ) A' m' u' (Foundations.RuntimePermutationWords.digit m' w' j) j hr hj
  have e := first.eqTrans (second.eqTrans ((selectedFactor.eqTrans originalCell).eqSymm))
  simpa only [Δ,j,A',B',m',w',u',Syn.shift,subst_choiceData,subst_scalarData,subst_factorData,subst_columns] using e

/-- The right factors use the choice word in the same column order. -/
theorem right_choice (A B m w u : PTm n) : Γ ⊢[PRAAx]
    choiceProduct rightEntry m m u (scalarData A B m w) ≐ rawProduct B m u := by
  apply GaussianRationalFiniteProduct.product_congr_bounded
  refine .allI (.impI ?_)
  let A' := Syn.shift A
  let B' := Syn.shift B
  let m' := Syn.shift m
  let w' := Syn.shift w
  let u' := Syn.shift u
  let j : PTm (n + 1) := var 0
  let Δ := lt j m' :: Γ.map Fm.shift
  have first := choice_body_at (Γ := Δ) rightEntry m' u' (scalarData A' B' m' w') j
  have second := right_entry_at (Γ := Δ) A' B' m' w' j (Foundations.RuntimePermutationWords.digit m' u' j)
  have third := factor_body_at (Γ := Δ) B' m' u' j
  have e := first.eqTrans (second.eqTrans third.eqSymm)
  simpa only [Δ,j,A',B',m',w',u',Syn.shift,subst_choiceData,subst_scalarData,subst_factorData] using e

theorem signed_choice_factor (A B m t u : PTm n) : Γ ⊢[PRAAx]
    inst3 signedChoiceEntry t u (scalarData A B m m) ≐
      qmul (rawProduct B m u) (signedTerm (columns A m u) m t) := by
  let w := wordCode m t
  have split := choice_product_split (Γ := Γ) m m u (scalarData A B m w)
  have factors := split.eqTrans (qmul_congr (left_choice A B m w u) (right_choice A B m w u))
  have first := (signed_choice_at (Γ := Γ) A B m t u).eqTrans (qmul_congr (.eqRefl (signPoint m w)) factors)
  have assoc := qmul_associative (Γ := Γ) (signPoint m w) (rawProduct (columns A m u) m w) (rawProduct B m u)
  exact first.eqTrans (assoc.eqSymm.eqTrans (qmul_commutative _ _))

theorem choice_column (A B m u : PTm n) : Γ ⊢[PRAAx]
    column signedChoiceEntry u (retainedCount m) (scalarData A B m m) ≐
      qmul (rawProduct B m u) (selectedDet A m u) := by
  let N := retainedCount m
  let p := pairT (columns A m u) m
  have terms : Γ ⊢[PRAAx] termsEqual (columnBody signedChoiceEntry) (multiplyBody signedBody)
      N (pairT u (scalarData A B m m)) (pairT (rawProduct B m u) p) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let m' := Syn.shift m
    let u' := Syn.shift u
    let N' := retainedCount m'
    let t : PTm (n + 1) := var 0
    let p' := pairT (columns A' m' u') m'
    let Δ := lt t N' :: Γ.map Fm.shift
    have first := column_entry (Γ := Δ) signedChoiceEntry t u' (scalarData A' B' m' m')
    have second := signed_choice_factor (Γ := Δ) A' B' m' t u'
    have third := (multiply_body_at (Γ := Δ) signedBody (rawProduct B' m' u') t p').eqTrans
      (qmul_congr (.eqRefl _) (signed_body_at (columns A' m' u') m' t))
    have e := first.eqTrans (second.eqTrans third.eqSymm)
    simpa only [Δ,N',p',t,A',B',m',u',N,p,Syn.shift,subst_pairT,subst_columns,subst_rawProduct,
      subst_scalarData,Foundations.RuntimePermutationWords.subst_count] using e
  have first := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms
  have second := sum_multiply (Γ := Γ) signedBody (rawProduct B m u) N p
  have third := qmul_congr (Prf.eqRefl (Γ := Γ) (rawProduct B m u)) (scalar_leibniz (columns A m u) m).eqSymm
  exact first.eqTrans (second.eqTrans third)

open GaussianRationalBlockSums (selectedBody filteredData maskBody mask_zero mask_kept filtered_sum selected_list_at)
open GaussianRationalFubini (columnSumBody column_sum_at)

/-- Read a signed word product before filtering by the permutation test. -/
def wordBody : PTm 2 :=
  qmul (signPoint (sndT (var 1)) (var 0)) (rawProduct (fstT (var 1)) (sndT (var 1)) (var 0))

theorem word_body_at (B m w : PTm n) : Γ ⊢[PRAAx]
    inst2 wordBody w (pairT B m) ≐ qmul (signPoint m w) (rawProduct B m w) := by
  let body : PTm 3 := qmul (signPoint (var 1) (var 2)) (rawProduct (var 0) (var 1) (var 2))
  have e := congrInst3 (Γ := Γ) body (fst_pair B m) (snd_pair B m) (Prf.eqRefl w)
  simpa only [body,wordBody,inst2,inst3,GaussianRationalHorner.subst_qmul,subst_signPoint,
    subst_rawProduct,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e

theorem scalar_filtered_word_sum (B m : PTm n) : Γ ⊢[PRAAx]
    scalarSum B m ≐
      GaussianRationalFiniteSum.sum (maskBody wordFilter wordBody) (wordLimit m) (pairT m (pairT B m)) := by
  let N := retainedCount m
  let data := filteredData (wordLimit m) m (pairT B m)
  have terms : Γ ⊢[PRAAx] termsEqual signedBody (selectedBody wordFilter wordBody) N (pairT B m) data := by
    refine .allI (.impI ?_)
    let B' := Syn.shift B
    let m' := Syn.shift m
    let t : PTm (n + 1) := var 0
    let Δ := lt t (retainedCount m') :: Γ.map Fm.shift
    have ht : Δ ⊢[PRAAx] lt t (retainedCount m') := Prf.hyp0
    have first := signed_body_at (Γ := Δ) B' m' t
    have second := selected_list_at (Γ := Δ) wordFilter wordBody (wordLimit m') m' (pairT B' m') t ht
    have third := word_body_at (Γ := Δ) B' m' (wordCode m' t)
    have e := first.eqTrans ((second.eqTrans third).eqSymm)
    simpa only [Δ,t,B',m',N,data,Syn.shift,subst_pairT,Foundations.RuntimePermutationWords.subst_horizon,
      GaussianRationalBlockSums.subst_filteredData,Foundations.RuntimePermutationWords.subst_count] using e
  have first := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms
  have second := filtered_sum (Γ := Γ) wordFilter wordBody (wordLimit m) m (pairT B m)
  exact first.eqTrans second

theorem choice_column_mask (A B m u : PTm n) (hu : Γ ⊢[PRAAx] lt u (wordLimit m)) :
    Γ ⊢[PRAAx]
    column signedChoiceEntry u (retainedCount m) (scalarData A B m m) ≐
      inst2 (multiplyBody (maskBody wordFilter wordBody)) u (pairT (scalarDet A m) (pairT m (pairT B m))) := by
  have middle := choice_column (Γ := Γ) A B m u
  have final := multiply_body_at (Γ := Γ) (maskBody wordFilter wordBody) (scalarDet A m) u (pairT m (pairT B m))
  refine middle.eqTrans (.orE (Foundations.RuntimePermutationWords.checker_cases m u) ?_ ?_)
  · have hbit : (wordBit m u ≐ zero) :: Γ ⊢[PRAAx] wordBit m u ≐ zero := Prf.hyp0
    have lhs := qmul_congr (Prf.eqRefl (rawProduct B m u))
      (GaussianScalarColumnSelection.selection_nonpermutation A m u hu.wk hbit)
    have mask := mask_zero wordFilter wordBody m (pairT B m) u
      (by simpa only [Foundations.RuntimePermutationWords.keep_at] using hbit)
    exact lhs.eqTrans ((qmul_zero_right _).eqTrans
      ((final.wk.eqTrans ((qmul_congr (.eqRefl _) mask).eqTrans (qmul_zero_right _))).eqSymm))
  · have hbit : (wordBit m u ≐ one) :: Γ ⊢[PRAAx] wordBit m u ≐ one := Prf.hyp0
    have lhs := qmul_congr (Prf.eqRefl (rawProduct B m u))
      (GaussianScalarColumnSelection.selection_permutation A m u hu.wk hbit)
    have hn : (wordBit m u ≐ one) :: Γ ⊢[PRAAx] neg (inst2 wordFilter u m ≐ zero) := by
      rw [Foundations.RuntimePermutationWords.keep_at]
      exact .impI (succ_ne_zero (hbit.wk.eqSymm.eqTrans Prf.hyp0))
    have mask := (mask_kept wordFilter wordBody m (pairT B m) u hn).eqTrans (word_body_at B m u)
    have assoc := qmul_associative (Γ := (wordBit m u ≐ one) :: Γ)
      (rawProduct B m u) (signPoint m u) (scalarDet A m)
    have al := assoc.eqSymm.eqTrans ((qmul_commutative _ _).eqTrans
      (qmul_congr (.eqRefl _) (qmul_commutative _ _)))
    exact lhs.eqTrans (al.eqTrans ((final.wk.eqTrans (qmul_congr (.eqRefl _) mask)).eqSymm))

theorem scalar_det_multiply (A B m : PTm n) : Γ ⊢[PRAAx]
    scalarDet (matrixProduct A B m) m ≐ qmul (scalarDet A m) (scalarDet B m) := by
  let N := retainedCount m
  let mask := maskBody wordFilter wordBody
  have terms : Γ ⊢[PRAAx] termsEqual (columnSumBody signedChoiceEntry) (multiplyBody mask)
      (wordLimit m) (pairT N (scalarData A B m m)) (pairT (scalarDet A m) (pairT m (pairT B m))) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let m' := Syn.shift m
    let N' := retainedCount m'
    let u : PTm (n + 1) := var 0
    let Δ := lt u (wordLimit m') :: Γ.map Fm.shift
    have hu : Δ ⊢[PRAAx] lt u (wordLimit m') := Prf.hyp0
    have e := (column_sum_at (Γ := Δ) signedChoiceEntry u N' (scalarData A' B' m' m')).eqTrans
      (choice_column_mask A' B' m' u hu)
    simpa only [Δ,u,N',A',B',m',N,Syn.shift,subst_pairT,Foundations.RuntimePermutationWords.subst_horizon,subst_scalarData,
      GaussianScalarDeterminant.subst_scalarDet,Foundations.RuntimePermutationWords.subst_count] using e
  have expanded := GaussianScalarDeterminantExpansion.determinant_choice_sum (Γ := Γ) A B m
  have byColumn := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms
  have factored := sum_multiply (Γ := Γ) mask (scalarDet A m) (wordLimit m) (pairT m (pairT B m))
  have tail := (scalar_filtered_word_sum (Γ := Γ) B m).eqSymm.eqTrans (scalar_leibniz B m).eqSymm
  exact expanded.eqTrans (byColumn.eqTrans (factored.eqTrans (qmul_congr (.eqRefl _) tail)))

theorem scalar_det_multiply_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scalarDet (matrixProduct (var 0) (var 1) (var 2)) (var 2) ≐
      qmul (scalarDet (var 0) (var 2)) (scalarDet (var 1) (var 2))) :=
  closeUniv 3 (scalar_det_multiply _ _ _)

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantMultiplication
