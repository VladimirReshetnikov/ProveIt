import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalLagrangeCardinals
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalPermutationSum
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows

/-!
# Actual Gaussian finite sums and scalar table products

The same existing sequence/Horner sum is split using its genuine segment
prefix theorem. Actual Kronecker weights select the canonical recode of
an arbitrary raw entry. Negation is transported as multiplication by the
fixed Gaussian minus one. No new sum recursion or desired sum law is an
input. All cuts, dimensions, tables, row/column positions and persistent
data are numerical. The scalar matrix product is the actual table of
these finite dot programs, with its shape and canonical cells derived.
This module asserts no inverse or determinant law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical recode_eq recode_represents)
open LeanProofs.IPRA.Analysis.GaussianInverseBinomialRows (negative_congr negative_product)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_canonical sum_index_congr sum_congr_bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalSumSegments (partialSum entriesEqual prefix_entries_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (delta table table_length table_row_length table_lookup)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The segment and the original offset body have the same bounded entries. -/
theorem segment_entries (f : PTm 2) (A B x : PTm n) : Γ ⊢[PRAAx]
    entriesEqual (GaussianRationalSumSegments.segment (sequence f (A+B) x) A B)
      (sequence (offB f) B (pairT A x)) B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (Syn.shift A+var 0) (Syn.shift A+Syn.shift B) := by
    ipra_le sl (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift B))
  have e := (GaussianRationalSumSegments.segment_lookup (Γ := Δ)
      (sequence f (Syn.shift A+Syn.shift B) (Syn.shift x)) (Syn.shift A) (Syn.shift B) (var 0) Prf.hyp0).eqTrans
    ((sequence_decode f (x := Syn.shift x) hi).eqTrans
      ((GaussianRationalFiniteProduct.offset_at f (Syn.shift A) (var 0) (Syn.shift x)).eqSymm.eqTrans
        (sequence_decode (offB f) (x := pairT (Syn.shift A) (Syn.shift x)) Prf.hyp0).eqSymm))
  simpa only [Δ,Syn.shift,GaussianRationalSumSegments.subst_segment,subst_sequence,
    PTm.subst_add,subst_pairT] using e

/-- A numerical cut of the SAME actual Gaussian sum, without another recursion. -/
theorem sum_split (f : PTm 2) (A B x : PTm n) : Γ ⊢[PRAAx]
    sum f (A+B) x ≐ qadd (sum f A x) (sum (offB f) B (pairT A x)) :=
  (GaussianRationalSumSegments.prefix_split (sequence f (A+B) x) A B B (le_refl _)).eqTrans
    (qadd_congr
      (GaussianRationalFiniteSum.generated_prefix_congr f (A+B) A x A (le_add_right _ _) (le_refl _))
      (prefix_entries_congr _ _ B B (segment_entries f A B x) (le_refl _)))

def zeroTerms (f : PTm 2) (N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ qzero)
@[simp] theorem subst_zeroTerms {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (N x : PTm n) :
    (zeroTerms f N x).subst σ = zeroTerms f (Syn.subst σ N) (Syn.subst σ x) := by
  simp [zeroTerms,Syn.subst_shift,Syn.shift_subst]

theorem zero_term_at (f : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] zeroTerms f N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 f i x ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ inst2 f i x ≐ qzero := by simpa [zeroTerms] using h.allE i
  exact .impE rule hi

theorem sum_zero_of_terms (f : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] zeroTerms f N x) : Γ ⊢[PRAAx]
    sum f N x ≐ qzero := by
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual f (qzero : PTm 2) N x x := by
    simpa only [zeroTerms,GaussianRationalFiniteSum.termsEqual,inst2,GaussianRationalHorner.subst_qzero] using h
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries).eqTrans (GaussianRationalFubini.zero_body_sum N x)

/-- Actual delta multiplication; its datum is the numerical pair (selected index, original data). -/
def deltaBody (f : PTm 2) : PTm 2 :=
  qmul (delta (fstT (var 1)) (var 0)) (inst2 f (var 0) (sndT (var 1)))
def deltaSum (f : PTm 2) (N c x : PTm n) : PTm n := sum (deltaBody f) N (pairT c x)
@[simp] theorem subst_deltaSum {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (N c x : PTm n) :
    Syn.subst σ (deltaSum f N c x) = deltaSum f (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ x) := by simp [deltaSum]

theorem delta_body_at (f : PTm 2) (c i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (deltaBody f) i (pairT c x) ≐ qmul (delta c i) (inst2 f i x) := by
  have e : Syn.subst ![i,pairT c x] (Syn.subst ![var 0,sndT (var 1)] f) =
      inst2 f i (sndT (pairT c x)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [deltaBody,inst2,GaussianRationalHorner.subst_qmul,GaussianRationalFiberVandermonde.subst_delta,
    subst_fstT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,e]
  exact qmul_congr (by
    unfold delta
    exact GaussianRationalMonicReconstruction.select_congr
      (AnalyticNumberTheory.Euler.congrEqb (fst_pair _ _) (.eqRefl _)) (.eqRefl _) (.eqRefl _))
    (congrInst2 f (.eqRefl _) (snd_pair _ _))

theorem delta_multiply_spike (c i q : PTm n) : Γ ⊢[PRAAx]
    qmul (delta c i) q ≐ GaussianRationalMonicReconstruction.spike c (recode q) i := by
  refine .orE (eq_or_ne i c) ?_ ?_
  · exact (qmul_congr (GaussianRationalLagrangeCardinals.delta_equal _ _ Prf.hyp0.eqSymm) (.eqRefl _)).eqTrans
      ((GaussianRationalFiniteProduct.raw_one_left q).eqTrans
        (GaussianRationalMonicReconstruction.spike_hit _ _ _ Prf.hyp0).eqSymm)
  · have hc : neg (i ≐ c) :: Γ ⊢[PRAAx] neg (c ≐ i) := .impI (.impE Prf.hyp1 Prf.hyp0.eqSymm)
    exact (qmul_congr (GaussianRationalLagrangeCardinals.delta_unequal _ _ hc) (.eqRefl _)).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_zero_left _).eqTrans
        (GaussianRationalMonicReconstruction.spike_miss _ _ _ Prf.hyp0).eqSymm)

/-- Bridge the actual delta product body to the already proved honest spike sum. -/
theorem delta_as_spike_sum (f : PTm 2) (N c x : PTm n) : Γ ⊢[PRAAx]
    deltaSum f N c x ≐ GaussianRationalPermutationSum.deltaSum f N c x := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT] using
    (delta_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) f (Syn.shift c) (var 0) (Syn.shift x)).eqTrans
      ((delta_multiply_spike (Syn.shift c) (var 0) (inst2 f (var 0) (Syn.shift x))).eqTrans
        (GaussianRationalPermutationSum.delta_body_at f (Syn.shift c) (var 0) (Syn.shift x)).eqSymm)

/-- Raw-safe selection: the actual fold returns the canonical recode. -/
theorem sum_delta (f : PTm 2) (N c x : PTm n) (hc : Γ ⊢[PRAAx] lt c N) : Γ ⊢[PRAAx]
    deltaSum f N c x ≐ recode (inst2 f c x) :=
  (delta_as_spike_sum _ _ _ _).eqTrans (GaussianRationalPermutationSum.delta_selected _ _ _ _ hc)
theorem sum_delta_canonical (f : PTm 2) (N c x : PTm n) (hc : Γ ⊢[PRAAx] lt c N)
    (hq : Γ ⊢[PRAAx] canonical (inst2 f c x)) : Γ ⊢[PRAAx] deltaSum f N c x ≐ inst2 f c x :=
  (sum_delta _ _ _ _ hc).eqTrans (recode_eq _ hq)
theorem sum_delta_outside (f : PTm 2) (N c x : PTm n) (hc : Γ ⊢[PRAAx] le N c) : Γ ⊢[PRAAx]
    deltaSum f N c x ≐ qzero :=
  (delta_as_spike_sum _ _ _ _).eqTrans (GaussianRationalPermutationSum.delta_outside _ _ _ _ hc)

def minusOne : PTm n := qnegative qone
@[simp] theorem subst_minusOne {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (minusOne : PTm n) = (minusOne : PTm l) := by simp [minusOne]

theorem negative_recode (q : PTm n) : Γ ⊢[PRAAx] qnegative (recode q) ≐ qnegative q :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (qnegative_canonical _) (qnegative_canonical _)
    (GaussianRationalL1.raw_den_positive q)
    (qnegative_represents _ _ _ (recode_represents q))
    (qnegative_represents _ _ _ (GaussianRationalL1.raw_represents q))

theorem negative_as_minusOne (q : PTm n) : Γ ⊢[PRAAx] qnegative q ≐ qmul minusOne q :=
  (negative_recode q).eqSymm.eqTrans
    ((negative_congr (GaussianRationalFiniteProduct.raw_one_left q)).eqSymm.eqTrans (negative_product qone q))

def negativeBody (f : PTm 2) : PTm 2 := qnegative f
@[simp] theorem negative_body_at (f : PTm 2) (i x : PTm n) :
    inst2 (negativeBody f) i x = qnegative (inst2 f i x) := by simp [negativeBody,inst2]

/-- Negation transport is genuine multiplication transport by fixed minus one. -/
theorem sum_negative (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sum (negativeBody f) N x ≐ qnegative (sum f N x) := by
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (negativeBody f)
      (GaussianRationalFiniteSum.multiplyBody f) N x (pairT minusOne x) := by
    refine .allI (.impI ?_)
    rw [negative_body_at,shift_pairT]
    simpa only [Syn.shift,subst_minusOne] using
      (negative_as_minusOne (inst2 f (var 0) (Syn.shift x))).eqTrans
        (GaussianRationalFiniteSum.multiply_body_at f minusOne (var 0) (Syn.shift x)).eqSymm
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply f minusOne N x).eqTrans (negative_as_minusOne _).eqSymm)

/-- Four exact persistent fields: the two original tables, row and column. -/
def scalarData (A B r j : PTm n) : PTm n := pairT A (pairT B (pairT r j))
def scalarFields (x : PTm n) : Fin 4 → PTm n :=
  ![fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))]
def scalarBody : PTm 2 := qmul
  (cell (scalarFields (var 1) 0) (scalarFields (var 1) 2) (var 0))
  (cell (scalarFields (var 1) 1) (var 0) (scalarFields (var 1) 3))
def scalarDot (A B m r j : PTm n) : PTm n := sum scalarBody m (scalarData A B r j)

@[simp] theorem subst_scalarData {l : ℕ} (σ : Fin n → PTm l) (A B r j : PTm n) :
    Syn.subst σ (scalarData A B r j) = scalarData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ j) := by simp [scalarData]
@[simp] theorem subst_scalarDot {l : ℕ} (σ : Fin n → PTm l) (A B m r j : PTm n) :
    Syn.subst σ (scalarDot A B m r j) = scalarDot (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ r) (Syn.subst σ j) := by simp [scalarDot]

theorem scalar_fields_at (A B r j : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    scalarFields (scalarData A B r j) i ≐ (![A,B,r,j] : Fin 4 → PTm n) i := by
  fin_cases i <;> simp only [scalarFields,scalarData,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three]
  · exact fst_pair _ _
  · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  · exact (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
  · exact (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

@[simp] theorem subst_scalarFields {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) (i : Fin 4) :
    Syn.subst σ (scalarFields x i) = scalarFields (Syn.subst σ x) i := by
  fin_cases i <;> simp [scalarFields]

theorem scalar_body_at (A B r j k : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody k (scalarData A B r j) ≐ qmul (cell A r k) (cell B k j) := by
  simp only [scalarBody,inst2,GaussianRationalHorner.subst_qmul,GaussianPolynomialDeterminantTerms.subst_cell,
    subst_scalarFields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr
    (entry_congr (entry_congr (scalar_fields_at A B r j 0) (scalar_fields_at A B r j 2)) (.eqRefl _))
    (entry_congr (entry_congr (scalar_fields_at A B r j 1) (.eqRefl _)) (scalar_fields_at A B r j 3))

theorem scalar_dot_canonical (A B m r j : PTm n) : Γ ⊢[PRAAx] canonical (scalarDot A B m r j) := sum_canonical _ _ _
theorem scalar_dot_zero (A B r j : PTm n) : Γ ⊢[PRAAx] scalarDot A B zero r j ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem scalar_dot_succ (A B m r j : PTm n) : Γ ⊢[PRAAx]
    scalarDot A B (succ m) r j ≐ qadd (scalarDot A B m r j) (qmul (cell A r m) (cell B m j)) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (scalar_body_at _ _ _ _ _))

/-- The table producer carries the original tables and the numerical dot count. -/
def productData (A B m : PTm n) : PTm n := pairT A (pairT B m)
def productBody : PTm 3 := scalarDot (fstT (var 2)) (fstT (sndT (var 2)))
  (sndT (sndT (var 2))) (var 0) (var 1)
def matrixProduct (A B m : PTm n) : PTm n := table productBody m m (productData A B m)
@[simp] theorem subst_productData {l : ℕ} (σ : Fin n → PTm l) (A B m : PTm n) :
    Syn.subst σ (productData A B m) = productData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) := by simp [productData]
@[simp] theorem subst_matrixProduct {l : ℕ} (σ : Fin n → PTm l) (A B m : PTm n) :
    Syn.subst σ (matrixProduct A B m) = matrixProduct (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) := by simp [matrixProduct]

theorem scalar_dot_congr {A A' B B' m m' r r' j j' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hr : Γ ⊢[PRAAx] r ≐ r') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    scalarDot A B m r j ≐ scalarDot A' B' m' r' j' :=
  sum_index_congr scalarBody hm (congrPairT hA (congrPairT hB (congrPairT hr hj)))

theorem product_body_at (A B m r j : PTm n) : Γ ⊢[PRAAx]
    Syn.subst ![r,j,productData A B m] productBody ≐ scalarDot A B m r j := by
  simp only [productBody,subst_scalarDot,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact scalar_dot_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _)

theorem product_length (A B m : PTm n) : Γ ⊢[PRAAx] length (matrixProduct A B m) ≐ m := table_length _ _ _ _
theorem product_row_length (A B m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (matrixProduct A B m) r) ≐ m := table_row_length _ _ _ _ _ hr
theorem product_lookup (A B m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (matrixProduct A B m) r j ≐ scalarDot A B m r j :=
  (table_lookup productBody m m (productData A B m) r j hr hj).eqTrans (product_body_at _ _ _ _ _)
theorem product_canonical (A B m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (matrixProduct A B m) r j) :=
  GaussianRationalHorner.canonical_congr (product_lookup _ _ _ _ _ hr hj) (scalar_dot_canonical _ _ _ _ _)

/-- Scalar square-table shape, without the unrelated polynomial cell-width predicate. -/
def squareShape (A m : PTm n) : Fm PTm n := (length A ≐ m) ⋏
  .all (lt (var 0) (Syn.shift m) ⟶ length (entry (Syn.shift A) (var 0)) ≐ Syn.shift m)
@[simp] theorem subst_squareShape {l : ℕ} (σ : Fin n → PTm l) (A m : PTm n) :
    (squareShape A m).subst σ = squareShape (Syn.subst σ A) (Syn.subst σ m) := by
  simp [squareShape,Syn.subst_shift,Syn.shift_subst]

theorem product_shape (A B m : PTm n) : Γ ⊢[PRAAx] squareShape (matrixProduct A B m) m := by
  refine .andI (product_length _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_matrixProduct] using
    product_row_length (Syn.shift A) (Syn.shift B) (Syn.shift m) (var 0) Prf.hyp0

/-- Actual payload, not a supplied product interface. It retains the independently
computed complete table and the selected original dot. -/
def output (A B m r j : PTm n) : PTm n := pairT (matrixProduct A B m) (scalarDot A B m r j)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A B m r j : PTm n) : PTm n := app outputF ![A,B,m,r,j]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (A B m r j : PTm n) :
    Syn.subst σ (output A B m r j) = output (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ r) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (A B m r j : PTm n) :
    Syn.subst σ (run A B m r j) = run (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ r) (Syn.subst σ j) := by
  simp [run]
  funext i
  fin_cases i <;> rfl

theorem program_at (A B m r j : PTm n) : Γ ⊢[PRAAx] run A B m r j ≐ output A B m r j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,B,m,r,j]
theorem returned_matrix (A B m r j : PTm n) : Γ ⊢[PRAAx]
    fstT (run A B m r j) ≐ matrixProduct A B m := (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_dot (A B m r j : PTm n) : Γ ⊢[PRAAx]
    sndT (run A B m r j) ≐ scalarDot A B m r j := (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_shape (A B m r j : PTm n) : Γ ⊢[PRAAx] squareShape (fstT (run A B m r j)) m := by
  have transport := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (squareShape (var 0) (var 1) : Fm PTm 2)
    ![matrixProduct A B m,m] ![fstT (run A B m r j),m] (fun i => by
      fin_cases i
      · exact (returned_matrix A B m r j).eqSymm
      · exact .eqRefl _)
  have rule : (Γ ⊢[PRAAx] squareShape (matrixProduct A B m) m) →
      (Γ ⊢[PRAAx] squareShape (fstT (run A B m r j)) m) := by
    simpa only [subst_squareShape,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using transport
  exact rule (product_shape A B m)
theorem returned_dot_canonical (A B m r j : PTm n) : Γ ⊢[PRAAx] canonical (sndT (run A B m r j)) :=
  GaussianRationalHorner.canonical_congr (returned_dot _ _ _ _ _) (scalar_dot_canonical _ _ _ _ _)
theorem returned_cell (A B m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (fstT (run A B m r j)) r j ≐ sndT (run A B m r j) :=
  (entry_congr (entry_congr (returned_matrix _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((product_lookup _ _ _ _ _ hr hj).eqTrans (returned_dot _ _ _ _ _).eqSymm)

theorem gaussian_sum_split_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sum f (var 0+var 1) (var 2) ≐ qadd (sum f (var 0) (var 2))
      (sum (offB f) (var 1) (pairT (var 0) (var 2)))) := closeUniv 3 (sum_split _ _ _ _)
theorem gaussian_zero_sum_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zeroTerms f (var 0) (var 1) ⟶ sum f (var 0) (var 1) ≐ qzero) :=
  closeUniv 2 (.impI (sum_zero_of_terms _ _ _ Prf.hyp0))
theorem gaussian_delta_sum_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ deltaSum f (var 0) (var 1) (var 2) ≐ recode (inst2 f (var 1) (var 2))) :=
  closeUniv 3 (.impI (sum_delta _ _ _ _ Prf.hyp0))
theorem gaussian_delta_canonical_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ canonical (inst2 f (var 1) (var 2)) ⟶
      deltaSum f (var 0) (var 1) (var 2) ≐ inst2 f (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (sum_delta_canonical _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem gaussian_negative_sum_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum (negativeBody f) (var 0) (var 1) ≐ qnegative (sum f (var 0) (var 1))) :=
  closeUniv 2 (sum_negative _ _ _)
theorem actual_scalar_dot_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((scalarDot (var 0) (var 1) zero (var 3) (var 4) ≐ qzero) ⋏
      scalarDot (var 0) (var 1) (succ (var 2)) (var 3) (var 4) ≐
        qadd (scalarDot (var 0) (var 1) (var 2) (var 3) (var 4))
          (qmul (cell (var 0) (var 3) (var 2)) (cell (var 1) (var 2) (var 4)))) :=
  closeUniv 5 (.andI (scalar_dot_zero _ _ _ _) (scalar_dot_succ _ _ _ _ _))
theorem actual_scalar_product_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (squareShape (matrixProduct (var 0) (var 1) (var 2)) (var 2)) :=
  closeUniv 3 (product_shape _ _ _)
theorem actual_scalar_product_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 2) ⟶ lt (var 4) (var 2) ⟶
      (cell (matrixProduct (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
        scalarDot (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      canonical (cell (matrixProduct (var 0) (var 1) (var 2)) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.andI (product_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (product_canonical _ _ _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_scalar_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (squareShape (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 2) ⋏
        canonical (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_shape _ _ _ _ _) (returned_dot_canonical _ _ _ _ _)))
theorem returned_scalar_product_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 2) ⟶ lt (var 4) (var 2) ⟶
      cell (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 3) (var 4) ≐
        sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_cell _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums
