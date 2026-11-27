import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianRealPart
import IPRADerivations.Analysis.Polynomials.Representation.GaussianEmbedding.RationalPolynomialGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpan
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.Subspaces.GaussianSuperellipticSubspaceFromSpan

/-!
# Original rational row combinations and embedded field spans

The rational producer sums original rational products. The forward witness is
the actual coefficient embedding; the reverse witness is the actual list of
real parts of arbitrary Gaussian coefficients. Neither direction assumes a
combination identity or restricts the Gaussian coefficient vector to the axis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalRowSpanGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup coefficients_length)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalFiberVandermonde (table table_length table_lookup table_row_length)
open GaussianRationalRowSpan (columnData combinationData)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def matrixBody : PTm 3 := embed (cell (var 2) (var 0) (var 1))
def matrix (A R N : PTm n) : PTm n := table matrixBody R N A
def realBody : PTm 2 := fstT (entry (var 1) (var 0))
def realVector (C R : PTm n) : PTm n := sequence realBody R C
def columnBody : PTm 2 := RationalArithmetic.multiply (entry (fstT (sndT (var 1))) (var 0))
  (cell (fstT (var 1)) (var 0) (sndT (sndT (var 1))))
def combinationAt (A R C j : PTm n) : PTm n := RationalFiniteSum.sum columnBody R (columnData A C j)
def combinationBody : PTm 2 := combinationAt (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def rowCombination (A R N C : PTm n) : PTm n := sequence combinationBody N (combinationData A R C)
def membership (A R N C v : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  RationalArgmin.rationalEq (entry (Syn.shift v) (var 0))
    (entry (rowCombination (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C)) (var 0)))
def hasCoefficients (A R N v : PTm n) : Fm PTm n := .ex
  ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v))

ipra_subst matrix
ipra_subst realVector
ipra_subst combinationAt
ipra_subst rowCombination
ipra_subst membership [Syn.subst_shift, Syn.shift_subst]
ipra_subst hasCoefficients [Syn.subst_shift, Syn.shift_subst]

theorem matrix_lookup (A R N i j : PTm n) (hi : Γ ⊢[PRAAx] lt i R) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] cell (matrix A R N) i j ≐ embed (cell A i j) := by
  simpa [matrix,matrixBody] using table_lookup matrixBody R N A i j hi hj
theorem matrix_shape (A R N : PTm n) : Γ ⊢[PRAAx] GaussianRationalRowElimination.shape (matrix A R N) R N := by
  refine .andI (table_length _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_matrix,matrix,GaussianRationalFiberVandermonde.subst_table] using table_row_length
    (Γ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) matrixBody (Syn.shift R) (Syn.shift N) (Syn.shift A) (var 0) Prf.hyp0
theorem real_vector_length (C R : PTm n) : Γ ⊢[PRAAx] length (realVector C R) ≐ R := sequence_length _ _ _
theorem real_vector_lookup (C R i : PTm n) (hi : Γ ⊢[PRAAx] lt i R) :
    Γ ⊢[PRAAx] entry (realVector C R) i ≐ fstT (entry C i) := by
  simpa [realVector,realBody,inst2] using sequence_decode (Γ := Γ) realBody (x := C) hi

theorem column_body_at (A C j i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term columnBody i (columnData A C j) ≐ RationalArithmetic.multiply (entry C i) (cell A i j) := by
  simp only [RationalFiniteSum.term,columnBody,inst2,RationalArithmetic.subst_multiply,subst_entry,
    GaussianPolynomialDeterminantTerms.subst_cell,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.multiply_congr (entry_congr (snd_pair _ _).fstE (.eqRefl _))
    (entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _).sndE)

theorem sum_congr (t : PTm 2) {N M x y : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] RationalFiniteSum.sum t N x ≐ RationalFiniteSum.sum t M y :=
  (RationalFiniteSum.sum_at t N x).eqSymm.eqTrans
    ((congrAp2 (RationalFiniteSum.sumCodeF t) hN hx).eqTrans (RationalFiniteSum.sum_at t M y))
theorem combination_congr {A B R S C D j k : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B) (hR : Γ ⊢[PRAAx] R ≐ S)
    (hC : Γ ⊢[PRAAx] C ≐ D) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] combinationAt A R C j ≐ combinationAt B S D k :=
  sum_congr columnBody hR (congrPairT hA (congrPairT hC hj))
theorem combination_body_at (A R C j : PTm n) : Γ ⊢[PRAAx]
    inst2 combinationBody j (combinationData A R C) ≐ combinationAt A R C j := by
  simp only [combinationBody,inst2,subst_combinationAt,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact combination_congr (fst_pair _ _) (snd_pair _ _).fstE
    (snd_pair _ _).sndE (.eqRefl _)
theorem combination_length (A R N C : PTm n) : Γ ⊢[PRAAx] length (rowCombination A R N C) ≐ N := sequence_length _ _ _
theorem combination_lookup (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] entry (rowCombination A R N C) j ≐ combinationAt A R C j :=
  (sequence_decode combinationBody hj).eqTrans (combination_body_at _ _ _ _)

theorem combination_embedding (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    embed (combinationAt A R C j) ≐ GaussianRationalRowSpan.combinationAt (matrix A R N) R (coefficients C R) j := by
  refine (RationalGaussianRealPart.embed_sum columnBody R (columnData A C j)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ R _ _ ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have hjs : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift.wk
  have lo := (RationalGaussianRealPart.embed_congr (column_body_at (Γ := Δ) (Syn.shift A) (Syn.shift C) (Syn.shift j) (var 0))).eqTrans
    (RationalGaussianEmbedding.embed_multiply _ _)
  have hi := (GaussianRationalRowSpan.column_body_at (Γ := Δ) (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
    (coefficients (Syn.shift C) (Syn.shift R)) (Syn.shift j) (var 0)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (coefficient_lookup _ _ _ Prf.hyp0) (matrix_lookup _ _ _ _ _ Prf.hyp0 hjs))
  simpa only [Δ,Syn.shift,RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed,
    RationalFiniteSum.term,GaussianRationalRowSpan.subst_columnData,subst_matrix,RationalPolynomialGaussianEmbedding.subst_coefficients] using lo.eqTrans hi.eqSymm

theorem combination_real_part (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    fstT (GaussianRationalRowSpan.combinationAt (matrix A R N) R C j) ≐ combinationAt A R (realVector C R) j := by
  refine (RationalGaussianRealPart.real_sum GaussianRationalRowSpan.columnBody R (columnData (matrix A R N) C j)).eqTrans
    (RationalFiniteSum.sum_ext _ _ R _ _ ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have hjs : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift.wk
  have lo := (congrFst ((GaussianRationalRowSpan.column_body_at (Γ := Δ)
    (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift C) (Syn.shift j) (var 0)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (matrix_lookup _ _ _ _ _ Prf.hyp0 hjs)))).eqTrans
        (RationalGaussianRealPart.real_product _ _)
  have hi := (column_body_at (Γ := Δ) (Syn.shift A) (realVector (Syn.shift C) (Syn.shift R)) (Syn.shift j) (var 0)).eqTrans
    (RationalAlgebra.multiply_congr (real_vector_lookup _ _ _ Prf.hyp0) (.eqRefl _))
  have eq := lo.eqTrans hi.eqSymm
  have val := RationalArgmin.rationalEq_congr (.eqRefl _) eq (.eqRefl _)
  simpa only [Δ,Syn.shift,RationalGaussianRealPart.realBody,RationalFiniteSum.term,inst2,subst_fstT,
    GaussianRationalRowSpan.subst_columnData,subst_matrix,subst_realVector] using val

theorem membership_at (A R N C v j : PTm n) (h : Γ ⊢[PRAAx] membership A R N C v) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] RationalArgmin.rationalEq (entry v j) (entry (rowCombination A R N C) j) := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ RationalArgmin.rationalEq (entry v j) (entry (rowCombination A R N C) j) := by
    ipra_simpa_inst [membership,Fm.subst_imp,RationalArgmin.subst_rationalEq,subst_lt,subst_entry,subst_rowCombination] using h.allE j
  exact .impE rule hj

theorem membership_embedding (A R N C v : PTm n) (h : Γ ⊢[PRAAx] membership A R N C v) : Γ ⊢[PRAAx]
    GaussianRationalRowSpan.membership (matrix A R N) R N (coefficients C R) (coefficients v N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C) (Syn.shift v) := by
    simpa only [Fm.shift,subst_membership,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have old := RationalArgmin.rationalEq_congr (.eqRefl _) (combination_lookup _ _ _ _ _ (Γ := Δ) Prf.hyp0)
    (membership_at _ _ _ _ _ _ hs.wk Prf.hyp0)
  have val := (RationalGaussianEmbedding.eq_iff (entry (Syn.shift v) (var 0))
    (combinationAt (Syn.shift A) (Syn.shift R) (Syn.shift C) (var 0))).iffMp old
  have lo := coefficient_lookup (Γ := Δ) (Syn.shift v) (Syn.shift N) (var 0) Prf.hyp0
  have hi := (GaussianRationalRowSpan.combination_lookup (Γ := Δ)
    (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N)
    (coefficients (Syn.shift C) (Syn.shift R)) (var 0) Prf.hyp0).eqTrans
      (combination_embedding _ _ _ _ _ Prf.hyp0).eqSymm
  have out := GaussianRationalValueEquality.value_equal_trans _ _ _ (GaussianRationalValueEquality.value_equal_of_code lo)
    (GaussianRationalValueEquality.value_equal_trans _ _ _ val (GaussianRationalValueEquality.value_equal_of_code hi.eqSymm))
  simpa only [Δ,Syn.shift,subst_matrix,RationalPolynomialGaussianEmbedding.subst_coefficients] using out

theorem recode_left_equal (a b : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalEq (RationalArithmetic.recode a) b) :
    Γ ⊢[PRAAx] RationalArgmin.rationalEq a b :=
  RationalGaussianEmbedding.rational_equal_of_scalar_recode a b
    ((RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.recode_guard a)).eqSymm.eqTrans
      (RationalGaussianEmbedding.scalar_recode_equal _ _ h))

theorem membership_real_part (A R N C v : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalRowSpan.membership (matrix A R N) R N C (coefficients v N)) :
    Γ ⊢[PRAAx] membership A R N (realVector C R) v := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalRowSpan.membership
      (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N) (Syn.shift C)
      (coefficients (Syn.shift v) (Syn.shift N)) := by
    simpa only [Fm.shift,GaussianRationalRowSpan.subst_membership,subst_matrix,
      RationalPolynomialGaussianEmbedding.subst_coefficients,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have val := RationalGaussianRealPart.real_values (Γ := Δ) _ _
    (GaussianRationalRowSpan.membership_at _ _ _ _ _ _ hs.wk Prf.hyp0)
  have lo := (coefficient_lookup (Γ := Δ) (Syn.shift v) (Syn.shift N) (var 0) Prf.hyp0).fstE
  have hi := (congrFst (GaussianRationalRowSpan.combination_lookup (Γ := Δ)
    (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N) (Syn.shift C) (var 0) Prf.hyp0)).eqTrans
      (combination_real_part _ _ _ _ _ Prf.hyp0)
  have raw := recode_left_equal _ _ (RationalArgmin.rationalEq_congr lo hi val)
  have out := RationalArgmin.rationalEq_congr (.eqRefl _)
    (combination_lookup (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N)
      (realVector (Syn.shift C) (Syn.shift R)) (var 0) Prf.hyp0).eqSymm raw
  simpa only [Δ,Syn.shift,subst_rowCombination,subst_realVector] using out

theorem rational_span_intro (A R N C v : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ R)
    (h : Γ ⊢[PRAAx] membership A R N C v) : Γ ⊢[PRAAx] hasCoefficients A R N v := by
  refine .exI C ?_
  simpa only [hasCoefficients,Fm.subst_and,Fm.subst_eq,Foundations.SequenceComposition.subst_length,subst_membership,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hC h
theorem gaussian_span_intro (A R N C v : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ R)
    (h : Γ ⊢[PRAAx] GaussianRationalRowSpan.membership A R N C v) :
    Γ ⊢[PRAAx] GaussianSuperellipticSubspaceFromSpan.hasCoefficients A R N v := by
  refine .exI C ?_
  simpa only [GaussianSuperellipticSubspaceFromSpan.hasCoefficients,Fm.subst_and,Fm.subst_eq,
    Foundations.SequenceComposition.subst_length,GaussianRationalRowSpan.subst_membership,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hC h

theorem span_embedding (A R N v : PTm n) (h : Γ ⊢[PRAAx] hasCoefficients A R N v) :
    Γ ⊢[PRAAx] GaussianSuperellipticSubspaceFromSpan.hasCoefficients (matrix A R N) R N (coefficients v N) := by
  refine .exE h ?_
  let Δ := ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v)) :: Γ.map Fm.shift
  have hm := membership_embedding (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v) (.andE₂ Prf.hyp0)
  have out := gaussian_span_intro _ _ _ _ _ (coefficients_length (var 0) (Syn.shift R)) hm
  simpa only [Δ,Fm.shift,GaussianSuperellipticSubspaceFromSpan.subst_hasCoefficients,
    subst_matrix,RationalPolynomialGaussianEmbedding.subst_coefficients,Syn.shift] using out

theorem span_real_part (A R N v : PTm n)
    (h : Γ ⊢[PRAAx] GaussianSuperellipticSubspaceFromSpan.hasCoefficients (matrix A R N) R N (coefficients v N)) :
    Γ ⊢[PRAAx] hasCoefficients A R N v := by
  refine .exE h ?_
  let Δ := ((length (var 0) ≐ Syn.shift R) ⋏ GaussianRationalRowSpan.membership
    (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N) (var 0)
      (coefficients (Syn.shift v) (Syn.shift N))) :: Γ.map Fm.shift
  have hm := membership_real_part (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v) (.andE₂ Prf.hyp0)
  have out := rational_span_intro _ _ _ _ _ (real_vector_length (var 0) (Syn.shift R)) hm
  simpa only [Δ,Fm.shift,subst_hasCoefficients,subst_matrix,
    RationalPolynomialGaussianEmbedding.subst_coefficients,Syn.shift] using out

theorem span_iff (A R N v : PTm n) : Γ ⊢[PRAAx] Fm.iff (hasCoefficients A R N v)
    (GaussianSuperellipticSubspaceFromSpan.hasCoefficients (matrix A R N) R N (coefficients v N)) :=
  .andI (.impI (span_embedding _ _ _ _ Prf.hyp0)) (.impI (span_real_part _ _ _ _ Prf.hyp0))

def matrixF : PR 3 := PTm.toPR (matrix (var 0) (var 1) (var 2))
def realVectorF : PR 2 := PTm.toPR (realVector (var 0) (var 1))
def combinationF : PR 4 := PTm.toPR (rowCombination (var 0) (var 1) (var 2) (var 3))
theorem matrix_at (A R N : PTm n) : Γ ⊢[PRAAx] ap3 matrixF A R N ≐ matrix A R N := by
  simpa [matrixF,ap3] using toPR_eq (Γ := Γ) (matrix (var 0) (var 1) (var 2) : PTm 3) ![A,R,N]
theorem real_vector_at (C R : PTm n) : Γ ⊢[PRAAx] ap2 realVectorF C R ≐ realVector C R := by
  simpa [realVectorF,ap2] using toPR_eq (Γ := Γ) (realVector (var 0) (var 1) : PTm 2) ![C,R]
theorem combination_at (A R N C : PTm n) : Γ ⊢[PRAAx] PTm.app combinationF ![A,R,N,C] ≐ rowCombination A R N C := by
  simpa [combinationF] using toPR_eq (Γ := Γ) (rowCombination (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,R,N,C]

theorem actual_embedded_matrix_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalRowElimination.shape (matrix (var 0) (var 1) (var 2)) (var 1) (var 2)) := closeUniv 3 (matrix_shape _ _ _)
theorem actual_embedded_matrix_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 2) ⟶ cell (matrix (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
      embed (cell (var 0) (var 3) (var 4))) := closeUniv 5 (.impI (.impI (matrix_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_real_vector_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ entry (realVector (var 0) (var 1)) (var 2) ≐ fstT (entry (var 0) (var 2))) :=
  closeUniv 3 (.impI (real_vector_lookup _ _ _ Prf.hyp0))
theorem actual_combination_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ embed (combinationAt (var 0) (var 1) (var 3) (var 4)) ≐
      GaussianRationalRowSpan.combinationAt (matrix (var 0) (var 1) (var 2)) (var 1) (coefficients (var 3) (var 1)) (var 4)) :=
  closeUniv 5 (.impI (combination_embedding _ _ _ _ _ Prf.hyp0))
theorem actual_combination_real_part_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ fstT (GaussianRationalRowSpan.combinationAt (matrix (var 0) (var 1) (var 2)) (var 1) (var 3) (var 4)) ≐
      combinationAt (var 0) (var 1) (realVector (var 3) (var 1)) (var 4)) :=
  closeUniv 5 (.impI (combination_real_part _ _ _ _ _ Prf.hyp0))
theorem actual_membership_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (membership (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ GaussianRationalRowSpan.membership
      (matrix (var 0) (var 1) (var 2)) (var 1) (var 2) (coefficients (var 3) (var 1)) (coefficients (var 4) (var 2))) :=
  closeUniv 5 (.impI (membership_embedding _ _ _ _ _ Prf.hyp0))
theorem actual_membership_real_part_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalRowSpan.membership (matrix (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3) (coefficients (var 4) (var 2)) ⟶
      membership (var 0) (var 1) (var 2) (realVector (var 3) (var 1)) (var 4)) :=
  closeUniv 5 (.impI (membership_real_part _ _ _ _ _ Prf.hyp0))
theorem actual_original_span_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (hasCoefficients (var 0) (var 1) (var 2) (var 3))
      (GaussianSuperellipticSubspaceFromSpan.hasCoefficients (matrix (var 0) (var 1) (var 2)) (var 1) (var 2)
        (coefficients (var 3) (var 2)))) := closeUniv 4 (span_iff _ _ _ _)
theorem actual_matrix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 matrixF (var 0) (var 1) (var 2) ≐ matrix (var 0) (var 1) (var 2)) := closeUniv 3 (matrix_at _ _ _)
theorem actual_real_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 realVectorF (var 0) (var 1) ≐ realVector (var 0) (var 1)) := closeUniv 2 (real_vector_at _ _)
theorem actual_combination_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app combinationF ![var 0,var 1,var 2,var 3] ≐ rowCombination (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (combination_at _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalRowSpanGaussianEmbedding
