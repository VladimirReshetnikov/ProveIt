import IPRADerivations.Analysis.RationalAnnihilatorOnSpan
import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums
import IPRADerivations.Foundations.RuntimePermutationWords

/-!
# Actual mask-selected subtuples span proper rational subspaces

A binary mask filters the original numerical positions. The returned subtuple
retains the original raw vector codes. Original membership in a proper span
supplies its computed annihilator, which also annihilates every selected row.
Thus the span of the actual subtuple is proper. Each selected original vector
belongs to that new span by its actual unit coefficient vector.

This is the finite-certificate normalization in the finite-observation cover
argument. It does not prove the quantitative finite-tuple Subspace Theorem or
that a bounded family of proper subspaces covers every source tuple.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSubtupleSpan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalRowSpanGaussianEmbedding (matrix matrix_shape matrix_lookup hasCoefficients span_embedding span_real_part)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr)
open RationalGaussianEmbedding (embed scalarOne)
open RationalSuperellipticSubspace (properSpan rank_deficit proper_of_deficit)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianRationalRowSpan (vectorDot)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def bit (mask i : PTm n) : PTm n := Foundations.RuntimePermutationWords.digit two mask i
def bitBody : PTm 2 := bit (var 1) (var 0)
def size (T mask : PTm n) : PTm n := Foundations.FilteredEnumerationCode.count bitBody (length T) mask
def indices (T mask : PTm n) : PTm n := Foundations.FilteredEnumerationCode.list bitBody (length T) mask
def selectedIndex (T mask r : PTm n) : PTm n := entry (indices T mask) r
def rowBody : PTm 2 := entry (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def selected (T mask : PTm n) : PTm n := sequence rowBody (size T mask) (pairT T (indices T mask))
def sourceMembers (A R N T mask : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift T)) ⟶ neg (bit (Syn.shift mask) (var 0) ≐ zero) ⟶
    hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (entry (Syn.shift T) (var 0)))
def dimensions (T N : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift T)) ⟶ length (entry (Syn.shift T) (var 0)) ≐ Syn.shift N)

@[simp] theorem subst_bit {q : ℕ} (σ : Fin n → PTm q) (mask i : PTm n) :
    Syn.subst σ (bit mask i) = bit (Syn.subst σ mask) (Syn.subst σ i) := by simp [bit,Foundations.RuntimePermutationWords.digit]
@[simp] theorem subst_size {q : ℕ} (σ : Fin n → PTm q) (T mask : PTm n) :
    Syn.subst σ (size T mask) = size (Syn.subst σ T) (Syn.subst σ mask) := by simp [size]
@[simp] theorem subst_indices {q : ℕ} (σ : Fin n → PTm q) (T mask : PTm n) :
    Syn.subst σ (indices T mask) = indices (Syn.subst σ T) (Syn.subst σ mask) := by simp [indices]
@[simp] theorem subst_selectedIndex {q : ℕ} (σ : Fin n → PTm q) (T mask r : PTm n) :
    Syn.subst σ (selectedIndex T mask r) = selectedIndex (Syn.subst σ T) (Syn.subst σ mask) (Syn.subst σ r) := by simp [selectedIndex]
@[simp] theorem subst_selected {q : ℕ} (σ : Fin n → PTm q) (T mask : PTm n) :
    Syn.subst σ (selected T mask) = selected (Syn.subst σ T) (Syn.subst σ mask) := by simp [selected]
@[simp] theorem subst_sourceMembers {q : ℕ} (σ : Fin n → PTm q) (A R N T mask : PTm n) :
    (sourceMembers A R N T mask).subst σ = sourceMembers (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ mask) := by simp [sourceMembers,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_dimensions {q : ℕ} (σ : Fin n → PTm q) (T N : PTm n) :
    (dimensions T N).subst σ = dimensions (Syn.subst σ T) (Syn.subst σ N) := by simp [dimensions,Syn.subst_shift,Syn.shift_subst]

theorem bit_body_at (mask i : PTm n) : inst2 bitBody i mask = bit mask i := by simp [bitBody,inst2]
theorem indices_length (T mask : PTm n) : Γ ⊢[PRAAx] length (indices T mask) ≐ size T mask :=
  Foundations.FilteredEnumerationCode.list_length _ _ _
theorem size_bound (T mask : PTm n) : Γ ⊢[PRAAx] le (size T mask) (length T) :=
  Foundations.FilteredEnumerationCode.count_le _ _ _
theorem selected_length (T mask : PTm n) : Γ ⊢[PRAAx] length (selected T mask) ≐ size T mask := sequence_length _ _ _
theorem selected_index_bound (T mask r : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    lt (selectedIndex T mask r) (length T) := Foundations.FilteredEnumerationCode.entry_bound _ _ _ _ hr
theorem selected_index_valid (T mask r : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    neg (bit mask (selectedIndex T mask r) ≐ zero) := by
  simpa only [bit_body_at,selectedIndex,indices] using Foundations.FilteredEnumerationCode.entry_valid (Γ := Γ) bitBody (length T) mask r hr

theorem row_body_at (T I r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (pairT T I) ≐ entry T (entry I r) := by
  simp only [rowBody,inst2,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (fst_pair _ _) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem selected_lookup (T mask r : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    entry (selected T mask) r ≐ entry T (selectedIndex T mask r) :=
  (sequence_decode rowBody (x := pairT T (indices T mask)) hr).eqTrans (row_body_at _ _ _)
theorem selected_cell (T mask r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    cell (selected T mask) r j ≐ entry (entry T (selectedIndex T mask r)) j :=
  entry_congr (selected_lookup T mask r hr) (.eqRefl _)
theorem retained_listed (T mask i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T))
    (hb : Γ ⊢[PRAAx] neg (bit mask i ≐ zero)) : Γ ⊢[PRAAx]
    lt (Foundations.FilteredEnumeration.rank bitBody i mask) (size T mask) ⋏
      selectedIndex T mask (Foundations.FilteredEnumeration.rank bitBody i mask) ≐ i := by
  exact Foundations.FilteredEnumerationCode.listed bitBody (length T) mask i hi (by simpa only [bit_body_at] using hb)
theorem selected_increasing (T mask r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s)
    (hs : Γ ⊢[PRAAx] lt s (size T mask)) : Γ ⊢[PRAAx] lt (selectedIndex T mask r) (selectedIndex T mask s) :=
  Foundations.FilteredEnumerationCode.increasing _ _ _ _ _ hrs hs

theorem source_member_at (A R N T mask i : PTm n) (h : Γ ⊢[PRAAx] sourceMembers A R N T mask)
    (hi : Γ ⊢[PRAAx] lt i (length T)) (hb : Γ ⊢[PRAAx] neg (bit mask i ≐ zero)) : Γ ⊢[PRAAx]
    hasCoefficients A R N (entry T i) := by
  have rule : Γ ⊢[PRAAx] lt i (length T) ⟶ neg (bit mask i ≐ zero) ⟶ hasCoefficients A R N (entry T i) := by
    simpa [sourceMembers] using h.allE i
  exact .impE (.impE rule hi) hb

theorem selected_source_member (A R N T mask r : PTm n) (h : Γ ⊢[PRAAx] sourceMembers A R N T mask)
    (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx] hasCoefficients A R N (entry T (selectedIndex T mask r)) :=
  source_member_at A R N T mask _ h (selected_index_bound T mask r hr) (selected_index_valid T mask r hr)

theorem selected_dimension (T mask N r : PTm n) (h : Γ ⊢[PRAAx] dimensions T N)
    (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx] length (entry (selected T mask) r) ≐ N := by
  have rule : Γ ⊢[PRAAx] lt (selectedIndex T mask r) (length T) ⟶
      length (entry T (selectedIndex T mask r)) ≐ N := by simpa [dimensions] using h.allE (selectedIndex T mask r)
  exact (congrFst (selected_lookup T mask r hr)).eqTrans
    (.impE rule (selected_index_bound T mask r hr))

theorem selected_row_dot (T mask N a r : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    GaussianRationalRowElimination.rowDot (matrix (selected T mask) (size T mask) N) N a r ≐
      vectorDot N (coefficients (entry T (selectedIndex T mask r)) N) a := by
  refine GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalRowElimination.dotBody
    GaussianRationalRowElimination.dotBody N
    (GaussianRationalRowElimination.dotData (matrix (selected T mask) (size T mask) N) a r)
    (GaussianRationalRowElimination.dotData (GaussianRationalMonicReduction.singleton
      (coefficients (entry T (selectedIndex T mask r)) N)) a zero) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hrs : Δ ⊢[PRAAx] lt (Syn.shift r) (size (Syn.shift T) (Syn.shift mask)) := by simpa [Fm.shift,Syn.shift] using hr.shift.wk
  have low := (GaussianRationalRowElimination.dot_body_at (Γ := Δ)
    (matrix (selected (Syn.shift T) (Syn.shift mask)) (size (Syn.shift T) (Syn.shift mask)) (Syn.shift N)) (Syn.shift a) (Syn.shift r) (var 0)).eqTrans
      (qmul_congr ((matrix_lookup _ _ _ _ _ hrs Prf.hyp0).eqTrans
        (embed_congr (selected_cell _ _ _ _ hrs))) (.eqRefl _))
  have high := (GaussianRationalRowSpan.vector_dot_term (Γ := Δ)
    (coefficients (entry (Syn.shift T) (selectedIndex (Syn.shift T) (Syn.shift mask) (Syn.shift r))) (Syn.shift N)) (Syn.shift a) (var 0)).eqTrans
      (qmul_congr (coefficient_lookup _ _ _ Prf.hyp0) (.eqRefl _))
  simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,RationalRowSpanGaussianEmbedding.subst_matrix,
    subst_selected,subst_size,subst_selectedIndex,Foundations.MasterCertificate.subst_entry,
    RationalPolynomialGaussianEmbedding.subst_coefficients,GaussianRationalMonicReduction.subst_singleton,
    ConciseIPRA.PTm.subst_zero] using low.eqTrans high.eqSymm

theorem selected_null (A R N T mask a : PTm n) (hm : Γ ⊢[PRAAx] sourceMembers A R N T mask)
    (ha : Γ ⊢[PRAAx] RationalOriginalAnnihilator.nullRows A R N a) : Γ ⊢[PRAAx]
    GaussianRationalRowElimination.nullRows (matrix (selected T mask) (size T mask) N) (size T mask) N (coefficients a N) := by
  have hms : Γ.map Fm.shift ⊢[PRAAx] sourceMembers (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift T) (Syn.shift mask) := by
    simpa [Fm.shift,Syn.shift] using hm.shift
  have has : Γ.map Fm.shift ⊢[PRAAx] RationalOriginalAnnihilator.nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (size (Syn.shift T) (Syn.shift mask)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (size (Syn.shift T) (Syn.shift mask)) := Prf.hyp0
  have member := selected_source_member _ _ _ _ _ _ (Γ := Δ) hms.wk hr
  have zeroDot := GaussianSuperellipticSubspaceFromSpan.span_dot_zero _ _ _ _ _
    (span_embedding _ _ _ _ member) (RationalAnnihilatorOnSpan.null_rows_embedding _ _ _ _ has.wk)
  simpa only [Δ,Syn.shift,subst_selected,subst_size,RationalRowSpanGaussianEmbedding.subst_matrix,
    RationalPolynomialGaussianEmbedding.subst_coefficients,GaussianRationalHorner.subst_qzero] using
    (selected_row_dot _ _ _ _ _ hr).eqTrans zeroDot

theorem embedded_unit_nonzero (a N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N)
    (hu : Γ ⊢[PRAAx] entry a s ≐ scalarOne) : Γ ⊢[PRAAx]
    GaussianRationalFreeColumnVector.nonzeroVector (coefficients a N) N := by
  have unit : Γ ⊢[PRAAx] entry (coefficients a N) s ≐ qone :=
    (coefficient_lookup a N s hs).eqTrans ((embed_congr hu).eqTrans RationalGaussianEmbedding.embed_one)
  have nz : Γ ⊢[PRAAx] neg (recode (entry (coefficients a N) s) ≐ qzero) :=
    .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
      (((recode_congr unit).eqTrans (recode_eq _ qone_canonical)).wk.eqSymm.eqTrans Prf.hyp0))
  refine .exI s ?_
  simpa [GaussianRationalFreeColumnVector.nonzeroVector] using Prf.andI hs nz

theorem selected_proper (A R N T mask : PTm n) (hp : Γ ⊢[PRAAx] properSpan A R N)
    (hm : Γ ⊢[PRAAx] sourceMembers A R N T mask) : Γ ⊢[PRAAx] properSpan (selected T mask) (size T mask) N := by
  let a := RationalOriginalAnnihilator.vector A R N
  have cert := RationalOriginalAnnihilator.certificate_of_deficit A R N (rank_deficit A R N hp)
  have hNull := selected_null A R N T mask a hm (.andE₂ (.andE₂ (.andE₂ cert)))
  have hNZ := embedded_unit_nonzero a N (RationalOriginalAnnihilator.free A R N)
    (.andE₁ (.andE₂ cert)) (.andE₁ (.andE₂ (.andE₂ cert)))
  exact proper_of_deficit _ _ _ (GaussianRationalRankNullityCriterion.nonzero_null_implies_deficit _ _ _ _
    (matrix_shape _ _ _) hNull hNZ)

/-- Fixed column reader used by the genuine finite delta sum. -/
def columnReader : PTm 2 := cell (fstT (var 1)) (var 0) (sndT (var 1))
theorem column_reader_at (A j i : PTm n) : Γ ⊢[PRAAx]
    inst2 columnReader i (pairT A j) ≐ cell A i j := by
  simp only [columnReader,inst2,GaussianPolynomialDeterminantTerms.subst_cell,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem unit_column (A R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    GaussianRationalRowSpan.combinationAt A R (GaussianRationalProperSpanWitness.unit R r) j ≐ recode (cell A r j) := by
  have same : Γ ⊢[PRAAx] GaussianRationalRowSpan.combinationAt A R (GaussianRationalProperSpanWitness.unit R r) j ≐
      GaussianRationalMatrixFiniteSums.deltaSum columnReader R r (pairT A j) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalRowSpan.columnBody
      (GaussianRationalMatrixFiniteSums.deltaBody columnReader) R
      (GaussianRationalRowSpan.columnData A (GaussianRationalProperSpanWitness.unit R r) j) (pairT r (pairT A j))
      (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
    have low := (GaussianRationalRowSpan.column_body_at (Γ := Δ) (Syn.shift A)
      (GaussianRationalProperSpanWitness.unit (Syn.shift R) (Syn.shift r)) (Syn.shift j) (var 0)).eqTrans
        (qmul_congr (GaussianRationalProperSpanWitness.unit_lookup _ _ _ Prf.hyp0) (.eqRefl _))
    have high := (GaussianRationalMatrixFiniteSums.delta_body_at (Γ := Δ) columnReader (Syn.shift r) (var 0)
      (pairT (Syn.shift A) (Syn.shift j))).eqTrans (qmul_congr (.eqRefl _) (column_reader_at _ _ _))
    simpa only [Δ,Syn.shift,GaussianRationalRowSpan.subst_columnData,GaussianRationalProperSpanWitness.subst_unit,
      subst_pairT] using low.eqTrans high.eqSymm
  exact same.eqTrans ((GaussianRationalMatrixFiniteSums.sum_delta columnReader R r (pairT A j) hr).eqTrans
    (recode_congr (column_reader_at A j r)))

/-- Every original rational row is in its own actual row span, including raw entries. -/
theorem row_belongs (A R N r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    hasCoefficients A R N (entry A r) := by
  apply span_real_part
  apply RationalRowSpanGaussianEmbedding.gaussian_span_intro _ _ _ (GaussianRationalProperSpanWitness.unit R r) _
    (GaussianRationalProperSpanWitness.unit_length R r)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hrs : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hr.shift.wk
  have hl := coefficient_lookup (Γ := Δ) (entry (Syn.shift A) (Syn.shift r)) (Syn.shift N) (var 0) Prf.hyp0
  have hc := matrix_lookup (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift r) (var 0) hrs Prf.hyp0
  have hu := (unit_column (Γ := Δ) (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R)
    (Syn.shift r) (var 0) hrs).eqTrans ((recode_congr hc).eqTrans (recode_eq _ (RationalGaussianEmbedding.embed_canonical _)))
  have hh := (GaussianRationalRowSpan.combination_lookup (Γ := Δ) (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
    (Syn.shift R) (Syn.shift N) (GaussianRationalProperSpanWitness.unit (Syn.shift R) (Syn.shift r)) (var 0) Prf.hyp0).eqTrans hu
  have value := GaussianRationalValueEquality.value_equal_of_code (hl.eqTrans hh.eqSymm)
  simpa only [Δ,Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,RationalPolynomialGaussianEmbedding.subst_coefficients,
    Foundations.MasterCertificate.subst_entry,GaussianRationalProperSpanWitness.subst_unit,
    GaussianRationalRowSpan.subst_rowCombination] using value

theorem selected_vector_belongs (T mask N r : PTm n) (hr : Γ ⊢[PRAAx] lt r (size T mask)) : Γ ⊢[PRAAx]
    hasCoefficients (selected T mask) (size T mask) N (entry T (selectedIndex T mask r)) := by
  have original := row_belongs (selected T mask) (size T mask) N r hr
  let φ := hasCoefficients (Syn.shift (selected T mask)) (Syn.shift (size T mask)) (Syn.shift N) (var 0)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (entry (selected T mask) r)) := by
    simpa only [φ,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using original
  simpa only [φ,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ (selected_lookup T mask r hr) start

theorem retained_vector_belongs (T mask N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T))
    (hb : Γ ⊢[PRAAx] neg (bit mask i ≐ zero)) : Γ ⊢[PRAAx]
    hasCoefficients (selected T mask) (size T mask) N (entry T i) := by
  have listed := retained_listed T mask i hi hb
  have member := selected_vector_belongs T mask N _ (.andE₁ listed)
  let φ := hasCoefficients (Syn.shift (selected T mask)) (Syn.shift (size T mask)) (Syn.shift N) (entry (Syn.shift T) (var 0))
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (selectedIndex T mask (Foundations.FilteredEnumeration.rank bitBody i mask))) := by
    simpa only [φ,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Foundations.MasterCertificate.subst_entry,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using member
  simpa only [φ,RationalRowSpanGaussianEmbedding.subst_hasCoefficients,Foundations.MasterCertificate.subst_entry,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.eqSubst1 φ (.andE₂ listed) start

def annihilator (A R N : PTm n) : PTm n := RationalOriginalAnnihilator.vector A R N
def certificate (A R N T mask : PTm n) : Fm PTm n :=
  properSpan (selected T mask) (size T mask) N ⋏
    (GaussianRationalRowElimination.nullRows (matrix (selected T mask) (size T mask) N) (size T mask) N
      (coefficients (annihilator A R N) N) ⋏
      ((length (annihilator A R N) ≐ N) ⋏ GaussianRationalFreeColumnVector.nonzeroVector (coefficients (annihilator A R N) N) N))
@[simp] theorem subst_annihilator {q : ℕ} (σ : Fin n → PTm q) (A R N : PTm n) :
    Syn.subst σ (annihilator A R N) = annihilator (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by simp [annihilator]
@[simp] theorem subst_certificate {q : ℕ} (σ : Fin n → PTm q) (A R N T mask : PTm n) :
    (certificate A R N T mask).subst σ = certificate (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ mask) := by simp [certificate]

theorem produced_certificate (A R N T mask : PTm n) (hp : Γ ⊢[PRAAx] properSpan A R N)
    (hm : Γ ⊢[PRAAx] sourceMembers A R N T mask) : Γ ⊢[PRAAx] certificate A R N T mask := by
  have cert := RationalOriginalAnnihilator.certificate_of_deficit A R N (rank_deficit A R N hp)
  exact .andI (selected_proper A R N T mask hp hm)
    (.andI (selected_null A R N T mask (annihilator A R N) hm (.andE₂ (.andE₂ (.andE₂ cert))))
      (.andI (.andE₁ cert) (embedded_unit_nonzero (annihilator A R N) N (RationalOriginalAnnihilator.free A R N)
        (.andE₁ (.andE₂ cert)) (.andE₁ (.andE₂ (.andE₂ cert))))))

/-- The actual program returns raw subtuple, original positions, count and the same annihilator. -/
def output (A R N T mask : PTm n) : PTm n := pairT (selected T mask)
  (pairT (indices T mask) (pairT (size T mask) (annihilator A R N)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R N T mask : PTm n) : PTm n := app outputF ![A,R,N,T,mask]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (A R N T mask : PTm n) :
    Syn.subst σ (output A R N T mask) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ mask) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (A R N T mask : PTm n) :
    Syn.subst σ (run A R N T mask) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ mask) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (A R N T mask : PTm n) : Γ ⊢[PRAAx] run A R N T mask ≐ output A R N T mask := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,N,T,mask]
theorem returned_selected (A R N T mask : PTm n) : Γ ⊢[PRAAx] fstT (run A R N T mask) ≐ selected T mask :=
  (congrFst (program_at A R N T mask)).eqTrans (fst_pair _ _)
theorem returned_indices (A R N T mask : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A R N T mask)) ≐ indices T mask :=
  (congrFst ((congrSnd (program_at A R N T mask)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_count (A R N T mask : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A R N T mask))) ≐ size T mask :=
  (congrFst ((congrSnd ((congrSnd (program_at A R N T mask)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_annihilator (A R N T mask : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run A R N T mask))) ≐ annihilator A R N :=
  (congrSnd ((congrSnd ((congrSnd (program_at A R N T mask)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_proper (A R N T mask : PTm n) (hp : Γ ⊢[PRAAx] properSpan A R N)
    (hm : Γ ⊢[PRAAx] sourceMembers A R N T mask) : Γ ⊢[PRAAx]
    properSpan (fstT (run A R N T mask)) (fstT (sndT (sndT (run A R N T mask)))) N := by
  simpa only [RationalSuperellipticSubspace.subst_properSpan,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (properSpan (var 0) (var 1) (var 2) : Fm PTm 3)
      ![selected T mask,size T mask,N] ![fstT (run A R N T mask),fstT (sndT (sndT (run A R N T mask))),N]
      (fun i => by fin_cases i; exact (returned_selected A R N T mask).eqSymm; exact (returned_count A R N T mask).eqSymm; exact .eqRefl N)
      (by simpa only [RationalSuperellipticSubspace.subst_properSpan,Syn.subst_var,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using selected_proper A R N T mask hp hm)

theorem actual_selected_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (selected (var 0) (var 1)) ≐ size (var 0) (var 1)) := closeUniv 2 (selected_length _ _)
theorem actual_selected_raw_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (size (var 0) (var 1)) ⟶ entry (selected (var 0) (var 1)) (var 2) ≐
      entry (var 0) (selectedIndex (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (selected_lookup _ _ _ Prf.hyp0))
theorem actual_row_belongs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ hasCoefficients (var 0) (var 1) (var 2) (entry (var 0) (var 3))) :=
  closeUniv 4 (.impI (row_belongs _ _ _ _ Prf.hyp0))
theorem actual_retained_vector_belongs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 0)) ⟶ neg (bit (var 1) (var 3) ≐ zero) ⟶
      hasCoefficients (selected (var 0) (var 1)) (size (var 0) (var 1)) (var 2) (entry (var 0) (var 3))) :=
  closeUniv 4 (.impI (.impI (retained_vector_belongs _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_selected_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (properSpan (var 0) (var 1) (var 2) ⟶ sourceMembers (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      properSpan (selected (var 3) (var 4)) (size (var 3) (var 4)) (var 2)) :=
  closeUniv 5 (.impI (.impI (selected_proper _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_subtuple_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (properSpan (var 0) (var 1) (var 2) ⟶ sourceMembers (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (produced_certificate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_subtuple_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_subtuple_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (properSpan (var 0) (var 1) (var 2) ⟶ sourceMembers (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      properSpan (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) (var 2)) :=
  closeUniv 5 (.impI (.impI (returned_proper _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalSubtupleSpan
