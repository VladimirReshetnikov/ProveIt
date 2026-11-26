import IPRADerivations.Analysis.Polynomials.RationalAnnihilatorPolynomial
import IPRADerivations.Analysis.Polynomials.RationalPolynomialWeightedDegreeGaussianEmbedding
import IPRADerivations.Foundations.SequenceEquality
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original rational annihilator nonvanishing and weight

Two bounded sequence inductions identify the constructed embedded table with
the actual Gaussian annihilator table, respecting both descending layouts.
A genuine bounded ORIGINAL rational nonzero coefficient witness derives
nonzero rows and the actual native rational weighted-degree bound <= L.
No target support, degree, maximum or polynomial identity is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalAnnihilatorPolynomialWeight

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalAnnihilatorPolynomial (polynomial)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr)
open RationalGaussianEmbedding (embed scalarZero)
open RationalRowSpanGaussianEmbedding (matrix matrixBody)
open GaussianPolynomialMultiplicationMatrix (slot slot_range)
open GaussianWeightedMonomialBasis (count)
open GaussianPolynomialMonicCompanion (rowShape)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.SequenceEquality (sequence_equal)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem actual_row_equal (a m e L r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.row matrixBody (succ L) (polynomial a m e L) r ≐
      GaussianAnnihilatorPolynomial.row (coefficients a (count m e L)) m e L (slot m r) := by
  apply sequence_equal (GaussianRationalFiberVandermonde.rowBody matrixBody) GaussianAnnihilatorPolynomial.rowBody
    (succ L) (pairT r (polynomial a m e L))
    (GaussianAnnihilatorPolynomial.rowData (coefficients a (count m e L)) m e L (slot m r))
  refine .allI (.impI ?_)
  let a' := Syn.shift a
  let m' := Syn.shift m
  let e' := Syn.shift e
  let L' := Syn.shift L
  let r' := Syn.shift r
  let Δ := lt (var 0) (succ L') :: Γ.map Fm.shift
  have ri : Δ ⊢[PRAAx] lt r' m' := by simpa [Δ,r',m',Fm.shift,Syn.shift] using hr.shift.wk
  have si : Δ ⊢[PRAAx] lt (var 0) (succ L') := Prf.hyp0
  have left : Δ ⊢[PRAAx] inst2 (GaussianRationalFiberVandermonde.rowBody matrixBody) (var 0)
      (pairT r' (polynomial a' m' e' L')) ≐ embed (GaussianPolynomialDeterminantTerms.cell (polynomial a' m' e' L') r' (var 0)) := by
    simpa only [matrixBody,RationalGaussianEmbedding.subst_embed,GaussianPolynomialDeterminantTerms.subst_cell,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      GaussianRationalFiberVandermonde.row_body_at (Γ := Δ) matrixBody (polynomial a' m' e' L') r' (var 0)
  have values := (embed_congr (RationalAnnihilatorPolynomial.stored_coefficient a' m' e' L' r' (var 0) ri si)).eqTrans
    (RationalAnnihilatorPolynomial.coefficient_embedding a' m' e' L' (slot m' r') (LeanProofs.IPRA.PTm.monus L' (var 0))
      (slot_range m' r' ri) (GaussianRationalMonicReconstruction.monus_le_left _ _))
  have right := GaussianAnnihilatorPolynomial.row_body_at (Γ := Δ) (coefficients a' (count m' e' L')) m' e' L' (slot m' r') (var 0)
  simpa only [Δ,a',m',e',L',r',Syn.shift,subst_pairT,RationalAnnihilatorPolynomial.subst_polynomial,
    GaussianAnnihilatorPolynomial.subst_rowData,RationalPolynomialGaussianEmbedding.subst_coefficients,
    GaussianWeightedMonomialBasis.subst_count,GaussianPolynomialMultiplicationMatrix.subst_slot,
    ConciseIPRA.PTm.subst_succ] using left.eqTrans (values.eqTrans right.eqSymm)

/-- Literal equality compares only these two actual constructed outer lists. -/
theorem matrix_equality (a m e L : PTm n) : Γ ⊢[PRAAx]
    matrix (polynomial a m e L) m (succ L) ≐
      GaussianAnnihilatorPolynomial.polynomial (coefficients a (count m e L)) m e L := by
  apply sequence_equal (GaussianRationalFiberVandermonde.tableBody matrixBody) GaussianAnnihilatorPolynomial.outerBody
    m (pairT (succ L) (polynomial a m e L))
    (GaussianAnnihilatorPolynomial.data (coefficients a (count m e L)) m e L)
  refine .allI (.impI ?_)
  let a' := Syn.shift a
  let m' := Syn.shift m
  let e' := Syn.shift e
  let L' := Syn.shift L
  let Δ := lt (var 0) m' :: Γ.map Fm.shift
  have same := actual_row_equal (Γ := Δ) a' m' e' L' (var 0) Prf.hyp0
  have left := GaussianRationalFiberVandermonde.table_body_at (Γ := Δ) matrixBody (succ L') (polynomial a' m' e' L') (var 0)
  have right := GaussianAnnihilatorPolynomial.outer_body_at (Γ := Δ) (coefficients a' (count m' e' L')) m' e' L' (var 0)
  simpa only [Δ,a',m',e',L',Syn.shift,subst_pairT,RationalAnnihilatorPolynomial.subst_polynomial,
    GaussianAnnihilatorPolynomial.subst_data,RationalPolynomialGaussianEmbedding.subst_coefficients,
    GaussianWeightedMonomialBasis.subst_count,ConciseIPRA.PTm.subst_succ] using left.eqTrans (same.eqTrans right.eqSymm)

def nonzeroLambda (a m e L : PTm n) : Fm PTm n := .ex
  (lt (var 0) (count (Syn.shift m) (Syn.shift e) (Syn.shift L)) ⋏
    neg (RationalArgmin.rationalEq (entry (Syn.shift a) (var 0)) scalarZero))
def input (a m e L : PTm n) : Fm PTm n := le one m ⋏ ((length a ≐ count m e L) ⋏ nonzeroLambda a m e L)
@[simp] theorem subst_nonzeroLambda {l : ℕ} (σ : Fin n → PTm l) (a m e L : PTm n) :
    (nonzeroLambda a m e L).subst σ = nonzeroLambda (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by
  simp [nonzeroLambda,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (a m e L : PTm n) :
    (input a m e L).subst σ = input (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by simp [input]

theorem gaussian_nonzero_lambda (a m e L : PTm n) (h : Γ ⊢[PRAAx] nonzeroLambda a m e L) : Γ ⊢[PRAAx]
    GaussianAnnihilatorPolynomial.nonzeroLambda (coefficients a (count m e L)) m e L := by
  refine .exE h ?_
  let a' := Syn.shift a
  let m' := Syn.shift m
  let e' := Syn.shift e
  let L' := Syn.shift L
  let Δ := (lt (var 0) (count m' e' L') ⋏ neg (RationalArgmin.rationalEq (entry a' (var 0)) scalarZero)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (count m' e' L') := .andE₁ Prf.hyp0
  have hn : Δ ⊢[PRAAx] neg (RationalArgmin.rationalEq (entry a' (var 0)) scalarZero) := .andE₂ Prf.hyp0
  have actual : Δ ⊢[PRAAx] GaussianTranslatedNonconstant.recode (entry (coefficients a' (count m' e' L')) (var 0)) ≐
      embed (entry a' (var 0)) :=
    (GaussianTranslatedNonconstant.recode_congr (coefficient_lookup a' (count m' e' L') (var 0) hr)).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _))
  have nz : Δ ⊢[PRAAx] neg (GaussianTranslatedNonconstant.recode (entry (coefficients a' (count m' e' L')) (var 0)) ≐ GaussianRationalHorner.qzero) :=
    .impI (.impE hn.wk ((RationalGaussianEmbedding.zero_iff _).iffMp (actual.wk.eqSymm.eqTrans Prf.hyp0)))
  have out : Δ ⊢[PRAAx] GaussianAnnihilatorPolynomial.nonzeroLambda (coefficients a' (count m' e' L')) m' e' L' := by
    refine .exI (var 0) ?_
    simpa [GaussianAnnihilatorPolynomial.nonzeroLambda] using Prf.andI hr nz
  simpa only [Δ,a',m',e',L',Fm.shift,Syn.shift,GaussianAnnihilatorPolynomial.subst_nonzeroLambda,
    RationalPolynomialGaussianEmbedding.subst_coefficients,GaussianWeightedMonomialBasis.subst_count,nonzeroLambda] using out

theorem gaussian_input (a m e L : PTm n) (h : Γ ⊢[PRAAx] input a m e L) : Γ ⊢[PRAAx]
    GaussianAnnihilatorPolynomial.input (coefficients a (count m e L)) m e L :=
  .andI (.andE₁ h) (.andI (RationalPolynomialGaussianEmbedding.coefficients_length _ _)
    (gaussian_nonzero_lambda a m e L (.andE₂ (.andE₂ h))))

private theorem gaussian_rows_congr (A B m L : PTm n) (he : Γ ⊢[PRAAx] A ≐ B)
    (h : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.nonzeroRows A m L) :
    Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.nonzeroRows B m L := by
  let φ := GaussianPolynomialWeightedDegree.nonzeroRows (var 0) (Syn.shift m) (Syn.shift L)
  have first : Γ ⊢[PRAAx] φ.subst (Syn.inst A) := by
    simpa only [φ,GaussianPolynomialWeightedDegree.subst_nonzeroRows,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h
  simpa only [φ,GaussianPolynomialWeightedDegree.subst_nonzeroRows,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.eqSubst1 φ he first

theorem nonzero_rows (a m e L : PTm n) (h : Γ ⊢[PRAAx] nonzeroLambda a m e L) : Γ ⊢[PRAAx]
    RationalPolynomialWeightedDegreeGaussianEmbedding.nonzeroRows (polynomial a m e L) m L :=
  RationalPolynomialWeightedDegreeGaussianEmbedding.nonzero_rows_from_gaussian _ _ _
    (gaussian_rows_congr _ _ m L (matrix_equality a m e L).eqSymm
      (GaussianAnnihilatorPolynomial.nonzero_rows _ _ _ _ (gaussian_nonzero_lambda a m e L h)))

private theorem gaussian_weight_congr (A B m L e : PTm n) (he : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.weightedDegree A m L e ≐ GaussianPolynomialWeightedDegree.weightedDegree B m L e := by
  ipra_congr (GaussianPolynomialWeightedDegree.weightedDegree (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [he, .eqRefl m, .eqRefl L, .eqRefl e]

theorem weighted_bound (a m e L : PTm n) (h : Γ ⊢[PRAAx] input a m e L) : Γ ⊢[PRAAx]
    le (RationalPolynomialWeightedDegreeGaussianEmbedding.weightedDegree (polynomial a m e L) m L e) L :=
  le_congr ((RationalPolynomialWeightedDegreeGaussianEmbedding.weighted_degree_conjugacy _ _ _ _).eqTrans
    (gaussian_weight_congr _ _ m L e (matrix_equality a m e L))).eqSymm (.eqRefl L)
    (GaussianAnnihilatorPolynomial.weighted_bound _ _ _ _ (gaussian_input a m e L h))

theorem flag_one (a m e L : PTm n) (h : Γ ⊢[PRAAx] nonzeroLambda a m e L) : Γ ⊢[PRAAx]
    RationalPolynomialWeightedDegreeGaussianEmbedding.flag (polynomial a m e L) m L e ≐ one :=
  RationalPolynomialWeightedDegreeGaussianEmbedding.flag_one_of_nonzero _ _ _ _ (nonzero_rows a m e L h)

theorem index_bound (a m e L : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    lt (RationalPolynomialWeightedDegreeGaussianEmbedding.index (polynomial a m e L) m L e) m :=
  RationalPolynomialWeightedDegreeGaussianEmbedding.index_bound _ _ _ _ hm

def certificate (a m e L : PTm n) : Fm PTm n := length (polynomial a m e L) ≐ m ⋏
  (rowShape (polynomial a m e L) m L ⋏
    (RationalPolynomialWeightedDegreeGaussianEmbedding.nonzeroRows (polynomial a m e L) m L ⋏
      le (RationalPolynomialWeightedDegreeGaussianEmbedding.weightedDegree (polynomial a m e L) m L e) L))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (a m e L : PTm n) :
    (certificate a m e L).subst σ = certificate (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by simp [certificate]

theorem polynomial_correct (a m e L : PTm n) (h : Γ ⊢[PRAAx] input a m e L) : Γ ⊢[PRAAx] certificate a m e L :=
  .andI (RationalAnnihilatorPolynomial.polynomial_length a m e L)
    (.andI (RationalAnnihilatorPolynomial.polynomial_shape a m e L)
      (.andI (nonzero_rows a m e L (.andE₂ (.andE₂ h))) (weighted_bound a m e L h)))

def output (a m e L : PTm n) : PTm n := pairT (polynomial a m e L)
  (pairT (RationalPolynomialWeightedDegreeGaussianEmbedding.flag (polynomial a m e L) m L e)
    (pairT (RationalPolynomialWeightedDegreeGaussianEmbedding.index (polynomial a m e L) m L e)
      (RationalPolynomialWeightedDegreeGaussianEmbedding.weightedDegree (polynomial a m e L) m L e)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (a m e L : PTm n) : PTm n := app outputF ![a,m,e,L]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (a m e L : PTm n) :
    Syn.subst σ (output a m e L) = output (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (a m e L : PTm n) :
    Syn.subst σ (run a m e L) = run (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (a m e L : PTm n) : Γ ⊢[PRAAx] run a m e L ≐ output a m e L := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,m,e,L]
theorem returned_polynomial (a m e L : PTm n) : Γ ⊢[PRAAx] fstT (run a m e L) ≐ polynomial a m e L :=
  (congrFst (program_at a m e L)).eqTrans (fst_pair _ _)
theorem returned_flag (a m e L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run a m e L)) ≐
    RationalPolynomialWeightedDegreeGaussianEmbedding.flag (polynomial a m e L) m L e :=
  (congrFst ((congrSnd (program_at a m e L)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_index (a m e L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run a m e L))) ≐
    RationalPolynomialWeightedDegreeGaussianEmbedding.index (polynomial a m e L) m L e :=
  (congrFst ((congrSnd ((congrSnd (program_at a m e L)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_weight (a m e L : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run a m e L))) ≐
    RationalPolynomialWeightedDegreeGaussianEmbedding.weightedDegree (polynomial a m e L) m L e :=
  (congrSnd ((congrSnd ((congrSnd (program_at a m e L)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_flag_one (a m e L : PTm n) (h : Γ ⊢[PRAAx] nonzeroLambda a m e L) : Γ ⊢[PRAAx]
    fstT (sndT (run a m e L)) ≐ one := (returned_flag a m e L).eqTrans (flag_one a m e L h)
theorem returned_index_bound (a m e L : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    lt (fstT (sndT (sndT (run a m e L)))) m :=
  lt_congr (returned_index a m e L).eqSymm (.eqRefl _) (index_bound a m e L hm)
theorem returned_weight_bound (a m e L : PTm n) (h : Γ ⊢[PRAAx] input a m e L) : Γ ⊢[PRAAx]
    le (sndT (sndT (sndT (run a m e L)))) L :=
  le_congr (returned_weight a m e L).eqSymm (.eqRefl _) (weighted_bound a m e L h)

theorem actual_annihilator_table_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (matrix (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (succ (var 3)) ≐
      GaussianAnnihilatorPolynomial.polynomial (coefficients (var 0) (count (var 1) (var 2) (var 3))) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (matrix_equality _ _ _ _)

theorem actual_rational_annihilator_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonzeroLambda (var 0) (var 1) (var 2) (var 3) ⟶
      RationalPolynomialWeightedDegreeGaussianEmbedding.nonzeroRows (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) :=
  closeUniv 4 (.impI (nonzero_rows _ _ _ _ Prf.hyp0))

theorem actual_rational_annihilator_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶
      le (RationalPolynomialWeightedDegreeGaussianEmbedding.weightedDegree
        (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (weighted_bound _ _ _ _ Prf.hyp0))

theorem actual_rational_annihilator_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (polynomial_correct _ _ _ _ Prf.hyp0))

theorem actual_rational_annihilator_weight_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem actual_returned_rational_annihilator_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) (var 3)) :=
  closeUniv 4 (.impI (returned_weight_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalAnnihilatorPolynomialWeight
