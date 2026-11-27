import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.Matrices.GaussianSuperellipticMatrixLeading
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticWordWeights
import IPRADerivations.Analysis.Polynomials.Determinants.Coefficients.GaussianPolynomialDeterminantTermDegree

/-!
# Original superelliptic cells in the actual determinant word product

Original polynomial shapes and the true nonzero f supply every actual
cell flag and degree law. Bounded individual observations identify the
existing determinant product's degree sum with the original-row candidate
sum. No generated matrix shape, factor law, successful product, or desired
degree bound is an incoming source hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticWordTerms

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (flag degree nonzeroCoefficients nonzero_of_flag_one degree_le)
open LeanProofs.IPRA.Analysis.GaussianPolynomialWeightedDegree
  (rowFlag rowDegree nonzeroRows weightedDegree)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries (matrix rowsInput entryPolynomial)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (width)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit horizon permutationBit)
open LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation (rotationCode)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (f G m a c : PTm n) : Fm PTm n := (length f ≐ succ c) ⋏
  (nonzeroCoefficients f c ⋏ GaussianPolynomialWeightedDegree.input G m a)
ipra_subst input
theorem rows_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx] rowsInput f G m a c :=
  .andI (.andE₁ (.andE₂ (.andE₂ h))) (.andI (.andE₁ h) (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))))
theorem matrix_shape (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.tableShape (matrix f G m a c) m (width m a c) :=
  GaussianPolynomialMonicNorm.multiplication_table_shape _ _ _ _ _
    (.andE₁ (rows_input _ _ _ _ _ h)) (.andE₂ (.andE₂ (rows_input _ _ _ _ _ h)))
theorem entry_input (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianSuperellipticMatrixEntries.input f G m a c (digit m w j) j :=
  .andI (rows_input _ _ _ _ _ h) (.andI (Foundations.RuntimePermutationWords.digit_bound m w j hj) hj)
theorem factor_flag (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    flag (GaussianPolynomialDeterminantTerms.factor (matrix f G m a c) m w j) (width m a c) ≐
      rowFlag G m a (GaussianSuperellipticWordWeights.rowIndex m w j) :=
  GaussianSuperellipticMatrixLeading.cell_flag f G m a c (digit m w j) j
    (entry_input _ _ _ _ _ _ _ h hj) (.andE₁ (.andE₂ h))

theorem factors_of_row_flags_prefix (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] le j m) (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.factorFlags (matrix f G m a c) m (width m a c) w j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hj.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift w) := by
    simpa only [Fm.shift,GaussianSuperellipticWordWeights.subst_rowFlags,Syn.shift] using hRows.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift j) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := lt_of_lt_of_le Prf.hyp0 js.wk
  simpa only [Δ,Syn.shift,GaussianSuperellipticMatrixEntries.subst_matrix,GaussianPolynomialMultiplicationMatrix.subst_width] using
    (factor_flag (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift w) (var 0) hs.wk range).eqTrans
      (GaussianSuperellipticWordWeights.row_flags_at _ _ _ _ _ rs.wk range)
theorem factors_of_row_flags (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.factorFlags (matrix f G m a c) m (width m a c) w m :=
  factors_of_row_flags_prefix _ _ _ _ _ _ _ h (le_refl m) hRows
theorem rows_of_factor_flags (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hFactors : Γ ⊢[PRAAx] GaussianPolynomialDeterminantTermDegree.factorFlags (matrix f G m a c) m (width m a c) w m) : Γ ⊢[PRAAx]
    GaussianSuperellipticWordWeights.rowFlags G m a w := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialDeterminantTermDegree.factorFlags
      (matrix (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)) (Syn.shift m)
        (width (Syn.shift m) (Syn.shift a) (Syn.shift c)) (Syn.shift w) (Syn.shift m) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTermDegree.subst_factorFlags,GaussianSuperellipticMatrixEntries.subst_matrix,
      GaussianPolynomialMultiplicationMatrix.subst_width,Syn.shift] using hFactors.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift] using (factor_flag (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (Syn.shift w) (var 0) hs.wk Prf.hyp0).eqSymm.eqTrans
      (GaussianPolynomialDeterminantTermDegree.factors_at _ _ _ _ _ _ fs.wk Prf.hyp0)
theorem factor_flags_iff (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    Fm.iff (GaussianPolynomialDeterminantTermDegree.factorFlags (matrix f G m a c) m (width m a c) w m)
      (GaussianSuperellipticWordWeights.rowFlags G m a w) :=
  .andI (.impI (rows_of_factor_flags _ _ _ _ _ _ h.wk Prf.hyp0))
    (.impI (factors_of_row_flags _ _ _ _ _ _ h.wk Prf.hyp0))

theorem factor_degree (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    degree (GaussianPolynomialDeterminantTerms.factor (matrix f G m a c) m w j) (width m a c) ≐
      GaussianSuperellipticWordWeights.candidate G m a (degree f c) w j :=
  (GaussianSuperellipticMatrixLeading.cell_degree f G m a c (digit m w j) j
    (entry_input _ _ _ _ _ _ _ h hj) (.andE₁ (.andE₂ h))
    (nonzero_of_flag_one _ _ (GaussianSuperellipticWordWeights.row_flags_at _ _ _ _ _ hRows hj))).eqTrans
      (congrAdd (.eqRefl _) (mul_comm _ _))
theorem candidate_body_at (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    inst2 (GaussianSuperellipticWordWeights.reader GaussianSuperellipticWordWeights.candidateSchema) j
      (GaussianSuperellipticWordWeights.data G m a d w) ≐ GaussianSuperellipticWordWeights.candidate G m a d w j := by
  have last : ![G,m,a,d,w,j] (5 : Fin 6) = j := rfl
  simpa only [GaussianSuperellipticWordWeights.candidateSchema,GaussianSuperellipticWordWeights.subst_candidate,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,last,Matrix.head_cons,Matrix.tail_cons] using
      GaussianSuperellipticWordWeights.reader_at (Γ := Γ) GaussianSuperellipticWordWeights.candidateSchema G m a d w j
theorem degree_sum (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] le j m) (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.degreeSum (matrix f G m a c) m (width m a c) w j ≐
      GaussianSuperellipticWordWeights.candidatePrefix G m a (degree f c) w j := by
  apply sum_congr_bounded
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hj.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift w) := by
    simpa only [Fm.shift,GaussianSuperellipticWordWeights.subst_rowFlags,Syn.shift] using hRows.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift j) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := lt_of_lt_of_le Prf.hyp0 js.wk
  have e := (GaussianPolynomialDeterminantTermDegree.degree_body_at (Γ := Δ)
    (matrix (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)) (Syn.shift m)
      (width (Syn.shift m) (Syn.shift a) (Syn.shift c)) (Syn.shift w) (var 0)).eqTrans
        ((factor_degree _ _ _ _ _ _ _ hs.wk range rs.wk).eqTrans
          (candidate_body_at (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (degree (Syn.shift f) (Syn.shift c))
            (Syn.shift w) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,GaussianSuperellipticMatrixEntries.subst_matrix,GaussianPolynomialMultiplicationMatrix.subst_width,
    GaussianPolynomialDeterminantTerms.subst_data,GaussianSuperellipticWordWeights.subst_data,GaussianRationalPolynomialDegree.subst_degree] using e

theorem stage_candidate (f G m a c w j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] le j m) (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    degree (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w j) (j*width m a c) ≐
      GaussianSuperellipticWordWeights.candidatePrefix G m a (degree f c) w j :=
  (GaussianPolynomialDeterminantTermDegree.stage_degree _ _ _ _ _
    (factors_of_row_flags_prefix _ _ _ _ _ _ _ h hj hRows)).eqTrans (degree_sum _ _ _ _ _ _ _ h hj hRows)
theorem stage_rows (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hStage : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m) (m*width m a c) ≐ one) : Γ ⊢[PRAAx]
    GaussianSuperellipticWordWeights.rowFlags G m a w :=
  rows_of_factor_flags _ _ _ _ _ _ h (GaussianPolynomialDeterminantTermDegree.stage_nonzero_factors _ _ _ _ _ hStage)
theorem stage_degree_le (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hStage : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m) (m*width m a c) ≐ one) : Γ ⊢[PRAAx]
    le (degree (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m) (m*width m a c))
      (weightedDegree G m a (degree f c)) := by
  have rows := stage_rows _ _ _ _ _ _ h hStage
  exact le_congr (stage_candidate _ _ _ _ _ _ _ h (le_refl m) rows).eqSymm (.eqRefl _)
    (GaussianSuperellipticWordWeights.word_degree_le _ _ _ _ _ (.andE₂ (.andE₂ h)) hw hp rows)
theorem stage_degree_strict (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hg : Γ ⊢[PRAAx] gcd m (degree f c) ≐ one)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hStage : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m) (m*width m a c) ≐ one)
    (hne : Γ ⊢[PRAAx] neg (w ≐ rotationCode m (GaussianPolynomialWeightedDegree.index G m a (degree f c)))) : Γ ⊢[PRAAx]
    lt (degree (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m) (m*width m a c))
      (weightedDegree G m a (degree f c)) := by
  have rows := stage_rows _ _ _ _ _ _ h hStage
  exact lt_congr (stage_candidate _ _ _ _ _ _ _ h (le_refl m) rows).eqSymm (.eqRefl _)
    (GaussianSuperellipticWordWeights.word_degree_strict _ _ _ _ _ (.andE₂ (.andE₂ h)) hg hw hp rows hne)
theorem signed_term_candidate (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hRows : Γ ⊢[PRAAx] GaussianSuperellipticWordWeights.rowFlags G m a w) : Γ ⊢[PRAAx]
    degree (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c) ≐
      GaussianSuperellipticWordWeights.candidatePrefix G m a (degree f c) w m :=
  (GaussianPolynomialDeterminantTermDegree.signed_term_degree _ _ _ _ (factors_of_row_flags _ _ _ _ _ _ h hRows)).eqTrans
    (degree_sum _ _ _ _ _ _ _ h (le_refl m) hRows)
theorem signed_term_rows (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hTerm : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c) ≐ one) : Γ ⊢[PRAAx]
    GaussianSuperellipticWordWeights.rowFlags G m a w :=
  rows_of_factor_flags _ _ _ _ _ _ h ((GaussianPolynomialDeterminantTermDegree.signed_term_flag_iff _ _ _ _).iffMp hTerm)
theorem signed_term_degree_le (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hTerm : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c) ≐ one) : Γ ⊢[PRAAx]
    le (degree (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c))
      (weightedDegree G m a (degree f c)) := by
  have rows := signed_term_rows _ _ _ _ _ _ h hTerm
  exact le_congr (signed_term_candidate _ _ _ _ _ _ h rows).eqSymm (.eqRefl _)
    (GaussianSuperellipticWordWeights.word_degree_le _ _ _ _ _ (.andE₂ (.andE₂ h)) hw hp rows)
theorem signed_term_degree_strict (f G m a c w : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hg : Γ ⊢[PRAAx] gcd m (degree f c) ≐ one)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hTerm : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c) ≐ one)
    (hne : Γ ⊢[PRAAx] neg (w ≐ rotationCode m (GaussianPolynomialWeightedDegree.index G m a (degree f c)))) : Γ ⊢[PRAAx]
    lt (degree (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w) (m*width m a c))
      (weightedDegree G m a (degree f c)) := by
  have rows := signed_term_rows _ _ _ _ _ _ h hTerm
  exact lt_congr (signed_term_candidate _ _ _ _ _ _ h rows).eqSymm (.eqRefl _)
    (GaussianSuperellipticWordWeights.word_degree_strict _ _ _ _ _ (.andE₂ (.andE₂ h)) hg hw hp rows hne)

def cyclicWord (f G m a c : PTm n) : PTm n := rotationCode m (GaussianPolynomialWeightedDegree.index G m a (degree f c))
ipra_subst cyclicWord
theorem rotation_rows (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianSuperellipticWordWeights.rowFlags G m a (cyclicWord f G m a c) :=
  GaussianSuperellipticWordWeights.rotation_row_flags _ _ _ _ (.andE₂ (.andE₂ h))
theorem rotation_factor_flags (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.factorFlags (matrix f G m a c) m (width m a c) (cyclicWord f G m a c) m :=
  factors_of_row_flags _ _ _ _ _ _ h (rotation_rows _ _ _ _ _ h)
theorem rotation_stage_success (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    flag (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) (cyclicWord f G m a c) m) (m*width m a c) ≐ one :=
  GaussianPolynomialDeterminantTermDegree.stage_success_of_factors _ _ _ _ _ (rotation_factor_flags _ _ _ _ _ h)
theorem rotation_stage_degree (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    degree (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) (cyclicWord f G m a c) m) (m*width m a c) ≐
      weightedDegree G m a (degree f c) :=
  (stage_candidate _ _ _ _ _ _ _ h (le_refl m) (rotation_rows _ _ _ _ _ h)).eqTrans
    (GaussianSuperellipticWordWeights.rotation_candidate _ _ _ _ (.andE₂ (.andE₂ h)))
theorem rotation_term_success (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    flag (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) (cyclicWord f G m a c)) (m*width m a c) ≐ one :=
  (GaussianPolynomialDeterminantTermDegree.signed_term_flag_iff _ _ _ _).iffMpr (rotation_factor_flags _ _ _ _ _ h)
theorem rotation_term_degree (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    degree (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) (cyclicWord f G m a c)) (m*width m a c) ≐
      weightedDegree G m a (degree f c) :=
  (signed_term_candidate _ _ _ _ _ _ h (rotation_rows _ _ _ _ _ h)).eqTrans
    (GaussianSuperellipticWordWeights.rotation_candidate _ _ _ _ (.andE₂ (.andE₂ h)))
theorem weighted_store_bound (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    le (weightedDegree G m a (degree f c)) (m*width m a c) :=
  le_congr (rotation_stage_degree _ _ _ _ _ h) (.eqRefl _) (degree_le _ _)

def cyclicCertificate (f G m a c : PTm n) : Fm PTm n :=
  (flag (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) (cyclicWord f G m a c) m) (m*width m a c) ≐ one) ⋏
    ((degree (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) (cyclicWord f G m a c) m) (m*width m a c) ≐
      weightedDegree G m a (degree f c)) ⋏
        ((flag (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) (cyclicWord f G m a c)) (m*width m a c) ≐ one) ⋏
          ((degree (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) (cyclicWord f G m a c)) (m*width m a c) ≐
            weightedDegree G m a (degree f c)) ⋏ le (weightedDegree G m a (degree f c)) (m*width m a c))))
ipra_subst cyclicCertificate
theorem cyclic_correct (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    cyclicCertificate f G m a c :=
  .andI (rotation_stage_success _ _ _ _ _ h) (.andI (rotation_stage_degree _ _ _ _ _ h)
    (.andI (rotation_term_success _ _ _ _ _ h) (.andI (rotation_term_degree _ _ _ _ _ h) (weighted_store_bound _ _ _ _ _ h))))

/-! No new fold is introduced: this PR6 only returns the original matrix,
the original determinant stage/term and their already existing sums. -/
def output (f G m a c w : PTm n) : PTm n := pairT (matrix f G m a c)
  (pairT (GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m)
    (pairT (GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w)
      (pairT (GaussianSuperellipticWordWeights.candidatePrefix G m a (degree f c) w m)
        (pairT (weightedDegree G m a (degree f c)) (cyclicWord f G m a c)))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (f G m a c w : PTm n) : PTm n := app outputF ![f,G,m,a,c,w]
def fields (p : PTm n) (i : Fin 6) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),
    fstT (sndT (sndT (sndT (sndT p)))),sndT (sndT (sndT (sndT (sndT p))))] i
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (f G m a c w : PTm n) : Γ ⊢[PRAAx] run f G m a c w ≐ output f G m a c w := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![f,G,m,a,c,w]
theorem returned_fields (f G m a c w : PTm n) (i : Fin 6) : Γ ⊢[PRAAx]
    fields (run f G m a c w) i ≐
      ![matrix f G m a c,GaussianPolynomialDeterminantTerms.stage (matrix f G m a c) m (width m a c) w m,
        GaussianPolynomialDeterminantTerms.term (matrix f G m a c) m (width m a c) w,
          GaussianSuperellipticWordWeights.candidatePrefix G m a (degree f c) w m,
            weightedDegree G m a (degree f c),cyclicWord f G m a c] i :=
  pairVectorField_eq 5 _ (program_at f G m a c w) i
theorem returned_rotation_degree (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    degree (fields (run f G m a c (cyclicWord f G m a c)) 1) (m*width m a c) ≐
      fields (run f G m a c (cyclicWord f G m a c)) 4 :=
  (GaussianPolynomialDeterminantTermDegree.degree_congr (returned_fields _ _ _ _ _ _ 1) (.eqRefl _)).eqTrans
    ((rotation_stage_degree _ _ _ _ _ h).eqTrans (returned_fields _ _ _ _ _ _ 4).eqSymm)

/-! All original data, counts, retained codes and prefix lengths are
numerical. The weak/strict guards are local nonzero-term branches; actual
cyclic success and degree require only the original source frame. -/
theorem actual_matrix_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianPolynomialDeterminantTerms.tableShape (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (width (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (matrix_shape _ _ _ _ _ Prf.hyp0))
theorem actual_factor_flags_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (GaussianPolynomialDeterminantTermDegree.factorFlags (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
        (var 2) (width (var 2) (var 3) (var 4)) (var 5) (var 2))
          (GaussianSuperellipticWordWeights.rowFlags (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (factor_flags_iff _ _ _ _ _ _ Prf.hyp0))
theorem actual_degree_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 6) (var 2) ⟶
      GaussianSuperellipticWordWeights.rowFlags (var 1) (var 2) (var 3) (var 5) ⟶
        GaussianPolynomialDeterminantTermDegree.degreeSum (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
          (var 2) (width (var 2) (var 3) (var 4)) (var 5) (var 6) ≐
            GaussianSuperellipticWordWeights.candidatePrefix (var 1) (var 2) (var 3) (degree (var 0) (var 4)) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (degree_sum _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_stage_degree_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (horizon (var 2)) ⟶ permutationBit (var 2) (var 5) ≐ one ⟶
      flag (GaussianPolynomialDeterminantTerms.stage (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
        (width (var 2) (var 3) (var 4)) (var 5) (var 2)) ((var 2)*width (var 2) (var 3) (var 4)) ≐ one ⟶
          le (degree (GaussianPolynomialDeterminantTerms.stage (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
            (width (var 2) (var 3) (var 4)) (var 5) (var 2)) ((var 2)*width (var 2) (var 3) (var 4)))
              (weightedDegree (var 1) (var 2) (var 3) (degree (var 0) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (stage_degree_le _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_strict_stage_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ gcd (var 2) (degree (var 0) (var 4)) ≐ one ⟶
      lt (var 5) (horizon (var 2)) ⟶ permutationBit (var 2) (var 5) ≐ one ⟶
        flag (GaussianPolynomialDeterminantTerms.stage (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
          (width (var 2) (var 3) (var 4)) (var 5) (var 2)) ((var 2)*width (var 2) (var 3) (var 4)) ≐ one ⟶
            neg ((var 5) ≐ cyclicWord (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
              lt (degree (GaussianPolynomialDeterminantTerms.stage (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
                (width (var 2) (var 3) (var 4)) (var 5) (var 2)) ((var 2)*width (var 2) (var 3) (var 4)))
                  (weightedDegree (var 1) (var 2) (var 3) (degree (var 0) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI (stage_degree_strict _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))
theorem actual_cyclic_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ cyclicCertificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (cyclic_correct _ _ _ _ _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_cyclic_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      degree (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (cyclicWord (var 0) (var 1) (var 2) (var 3) (var 4))) 1)
        ((var 2)*width (var 2) (var 3) (var 4)) ≐
          fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (cyclicWord (var 0) (var 1) (var 2) (var 3) (var 4))) 4) :=
  closeUniv 5 (.impI (returned_rotation_degree _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticWordTerms
