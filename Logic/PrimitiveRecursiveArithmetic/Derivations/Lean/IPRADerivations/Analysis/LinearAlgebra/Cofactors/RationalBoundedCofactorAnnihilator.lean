import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalCofactorDotProduct
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalCofactorOriginalClearing
import IPRADerivations.Analysis.RationalArithmetic.Spans.RankAndAnnihilators.RationalOriginalAnnihilator

/-!
# The bounded integer annihilator of the original rational rows

For a matrix of deficient determinantal rank, the actual signed integer
cofactor vector is nonzero and annihilates the original rational rows.
The common denominator relating the two row products is positive and
cancels. The original coefficient bound applies to this same vector.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBoundedCofactorAnnihilator

open_ipra
open RationalMaximalMinors (rank)
open RationalMinorFreeColumn (free free_column_spec)
open RationalCofactorVector (vector vector_length vector_nonzero vector_bound)
open RationalCofactorCoefficientValues (coefficientValue subst_coefficientValue)
open RationalCofactorDotProduct (clearedDot clearedBody cleared_body_at cleared_dot_zero)
open RationalCofactorBorderedRows (data subst_data)
open RationalCofactorOriginalClearing (cleared_cell_scale cancel_embedded_zero)
open RationalSelectedMinors (scale subst_scale)
open RationalOriginalAnnihilator (rowDot dotBody dot_body_at nullRows)
open RationalGaussianEmbedding (embed scalarZero embed_multiply)
open RationalGaussianRealPart (embedBody embed_sum real_zero)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalSupMetric (coordinate)
open RationalCofactorMinorBounds (bound)
open RationalMatrixClearingBounds (inputMatrix)
open RationalMatrixInputHeight (height height_positive input_height)
open GaussianRationalRowElimination (dotData subst_dotData)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalFiniteSum (termsEqual multiplyBody multiply_body_at sum_multiply)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rationalBody : PTm 2 := coefficientValue (fstT (var 1)) (sndT (var 1)) (var 0)
def rationalVector (P d : PTm n) : PTm n := sequence rationalBody d (pairT P d)

ipra_subst rationalVector

theorem rational_vector_length (P d : PTm n) : Γ ⊢[PRAAx] length (rationalVector P d) ≐ d :=
  sequence_length rationalBody d (pairT P d)

theorem rational_vector_lookup (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) :
    Γ ⊢[PRAAx] entry (rationalVector P d) j ≐ coefficientValue P d j := by
  refine (sequence_decode rationalBody (x := pairT P d) hj).eqTrans ?_
  simp only [rationalBody,inst2,subst_coefficientValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (coefficientValue (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl j]

private theorem embed_dot_term (P d i j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) :
    Γ ⊢[PRAAx] inst2 (embedBody dotBody) j (dotData P (rationalVector P d) i) ≐
      qmul (embed (coefficientValue P d j)) (embed (cell P i j)) := by
  let v := rationalVector P d
  let a := cell P i j
  have h := (dot_body_at (Γ := Γ) P v i j).eqTrans
    (RationalAlgebra.multiply_congr (rational_vector_lookup P d j hj) (.eqRefl a))
  simpa only [embedBody,inst2,RationalGaussianEmbedding.subst_embed] using
    (embed_congr h).eqTrans (embed_multiply (coefficientValue P d j) a)

private theorem clearing_term (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx] inst2 clearedBody j (data P d i) ≐
      inst2 (multiplyBody (embedBody dotBody)) j (pairT (scale P d) (dotData P (rationalVector P d) i)) := by
  let a := embed (coefficientValue P d j)
  let b := embed (cell P i j)
  let D := scale P d
  have rearrange : Γ ⊢[PRAAx] qmul a (qmul D b) ≐ qmul D (qmul a b) :=
    (qmul_associative a D b).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative a D) (.eqRefl b)).eqTrans (qmul_associative D a b))
  exact (cleared_body_at P d i j).eqTrans
    ((qmul_congr (.eqRefl a) (cleared_cell_scale P d i j hi hj)).eqTrans
      (rearrange.eqTrans ((multiply_body_at _ _ _ _).eqTrans
        (qmul_congr (.eqRefl D) (embed_dot_term P d i j hj))).eqSymm))

theorem cleared_eq_scaled_original (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) :
    Γ ⊢[PRAAx] clearedDot P d i ≐ qmul (scale P d) (embed (rowDot P d (rationalVector P d) i)) := by
  let x := data P d i
  let y := dotData P (rationalVector P d) i
  let D := scale P d
  let g := embedBody dotBody
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift P)) := by
    simpa only [Fm.shift,Syn.shift,subst_lt,Foundations.SequenceComposition.subst_length] using hi.shift
  have ht : Γ ⊢[PRAAx] termsEqual clearedBody (multiplyBody g) d x (pairT D y) := by
    refine .allI (.impI ?_)
    simpa only [x,y,D,g,Syn.shift,subst_data,subst_pairT,subst_scale,subst_dotData,subst_rationalVector] using
      clearing_term (Syn.shift P) (Syn.shift d) (Syn.shift i) (var 0) hi'.wk Prf.hyp0
  exact (GaussianRationalFiniteSum.sum_congr_bounded clearedBody (multiplyBody g) d x (pairT D y) ht).eqTrans
    ((sum_multiply g D d y).eqTrans (qmul_congr (.eqRefl D) (embed_sum dotBody d y).eqSymm))

theorem original_row_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx] rowDot P d (rationalVector P d) i ≐ scalarZero := by
  let y := dotData P (rationalVector P d) i
  let q := rowDot P d (rationalVector P d) i
  have hq : Γ ⊢[PRAAx] RationalNormalForm.wellFormed q := RationalFiniteSum.sum_well_formed dotBody d y
  have z := cancel_embedded_zero P d q
    ((cleared_eq_scaled_original P d i hi).eqSymm.eqTrans (cleared_dot_zero P d i h hi))
  exact (RationalNormalForm.normalize_fixed_point q hq).eqSymm.eqTrans
    ((fst_pair (RationalArithmetic.recode q) scalarZero).eqSymm.eqTrans ((congrFst z).eqTrans real_zero))

theorem original_null_rows (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] nullRows P (length P) d (rationalVector P d) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] lt (rank (Syn.shift P) (Syn.shift d)) (Syn.shift d) := by
    simpa only [Fm.shift,Syn.shift,subst_lt,RationalMaximalMinors.subst_rank] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,Foundations.SequenceComposition.subst_length,subst_rationalVector] using
    original_row_zero (Syn.shift P) (Syn.shift d) (var 0) h'.wk Prf.hyp0

/-- The source uniform bound concerns the integer entries of the returned vector. -/
def coefficientBounds (P d H w : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift d) ⟶ le (zabs (coordinate (Syn.shift w) (var 0)))
    (bound (Syn.shift P) (Syn.shift d) (Syn.shift H)))

theorem coefficient_bounds (P d H : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hH : Γ ⊢[PRAAx] le one H) (hP : Γ ⊢[PRAAx] inputMatrix P d H) :
    Γ ⊢[PRAAx] coefficientBounds P d H (vector P d) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] lt (rank (Syn.shift P) (Syn.shift d)) (Syn.shift d) := by
    simpa only [Fm.shift,Syn.shift,subst_lt,RationalMaximalMinors.subst_rank] using h.shift
  have hH' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by
    simpa [Fm.shift,Syn.shift] using hH.shift
  have hP' : Γ.map Fm.shift ⊢[PRAAx] inputMatrix (Syn.shift P) (Syn.shift d) (Syn.shift H) := by
    simpa only [Fm.shift,Syn.shift,RationalMatrixClearingBounds.subst_inputMatrix] using hP.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,RationalCofactorVector.subst_vector] using
    vector_bound (Syn.shift P) (Syn.shift d) (Syn.shift H) (var 0) h'.wk Prf.hyp0 hH'.wk hP'.wk

/-- The integer result, its exact rational interpretation and its source bound. -/
def certificate (P d : PTm n) : Fm PTm n :=
  (length (vector P d) ≐ d) ⋏
    (lt (free P d) d ⋏
      (neg (ZT.eq (coordinate (vector P d) (free P d)) (ZT.ofNat zero)) ⋏
        (nullRows P (length P) d (rationalVector P d) ⋏ coefficientBounds P d (height P d) (vector P d))))

theorem certificate_of_rank (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] certificate P d :=
  .andI (vector_length P d) (.andI (free_column_spec P d h).andE₁ (.andI (vector_nonzero P d h)
    (.andI (original_null_rows P d h) (coefficient_bounds P d (height P d) h (height_positive P d) (input_height P d)))))

theorem actual_cofactor_original_row_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      rowDot (var 0) (var 1) (rationalVector (var 0) (var 1)) (var 2) ≐ scalarZero) :=
  closeUniv 3 (.impI (.impI (original_row_zero _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_cofactor_source_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ le one (var 2) ⟶ inputMatrix (var 0) (var 1) (var 2) ⟶
      coefficientBounds (var 0) (var 1) (var 2) (vector (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (coefficient_bounds _ _ _ (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

theorem actual_bounded_cofactor_annihilator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (certificate_of_rank _ _ Prf.hyp0))

theorem actual_cofactor_rational_coordinate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶
      entry (rationalVector (var 0) (var 1)) (var 2) ≐ coefficientValue (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (rational_vector_lookup _ _ _ Prf.hyp0))

theorem actual_bounded_cofactor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶
      (RationalCofactorVector.run (var 0) (var 1) ≐ vector (var 0) (var 1)) ⋏ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (.andI (RationalCofactorVector.program_at _ _) (certificate_of_rank _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalBoundedCofactorAnnihilator
