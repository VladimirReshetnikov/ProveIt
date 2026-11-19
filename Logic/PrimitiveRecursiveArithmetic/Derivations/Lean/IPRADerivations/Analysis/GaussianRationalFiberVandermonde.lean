import IPRADerivations.Analysis.GaussianRationalCurveFibers
import IPRADerivations.Analysis.GaussianPolynomialMonicNorm

/-!
# Actual numerical fiber Vandermonde rows and polynomial row products

The original ordinate list produces the rectangular power table and its
square completion by standard coordinate rows. A genuine polynomial fold
multiplies this square table by the original polynomial matrix. Its
coefficient and evaluator formulas are derived by QF induction. Original
curve/function equations then annihilate the first actual fiber rows.
No inverse, determinant law or norm multiplicity is asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence subst_entry subst_sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qadd_congr qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (singleton singleton_length singleton_lookup singleton_evaluation evaluate_congr
    zeros_congr zeros_canonical added_canonical canonical_coefficients_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_lookup zeros_evaluation added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell rowCells tableShape cell_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A fixed cell body reads numerical row, column and persistent data. -/
def rowBody (f : PTm 3) : PTm 2 := Syn.subst ![fstT (var 1),var 0,sndT (var 1)] f
def row (f : PTm 3) (b x r : PTm n) : PTm n := sequence (rowBody f) b (pairT r x)
def tableBody (f : PTm 3) : PTm 2 := row f (fstT (var 1)) (sndT (var 1)) (var 0)
def table (f : PTm 3) (a b x : PTm n) : PTm n := sequence (tableBody f) a (pairT b x)

@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (f : PTm 3) (b x r : PTm n) :
    Syn.subst σ (row f b x r) = row f (Syn.subst σ b) (Syn.subst σ x) (Syn.subst σ r) := by simp [row]
@[simp] theorem subst_table {l : ℕ} (σ : Fin n → PTm l) (f : PTm 3) (a b x : PTm n) :
    Syn.subst σ (table f a b x) = table f (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by simp [table]

theorem row_body_at (f : PTm 3) (x r j : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowBody f) j (pairT r x) ≐ Syn.subst ![r,j,x] f := by
  simp only [rowBody,inst2,Syn.subst_subst,subst_fstT,subst_sndT,Syn.subst_var]
  apply Prf.eqCongr (Ax := PRAAx) f
  intro i
  fin_cases i
  · simpa using (fst_pair (Γ := Γ) r x)
  · exact .eqRefl _
  · simpa using (snd_pair (Γ := Γ) r x)
theorem row_length (f : PTm 3) (b x r : PTm n) : Γ ⊢[PRAAx] length (row f b x r) ≐ b := sequence_length _ _ _
theorem row_lookup (f : PTm 3) (b x r j : PTm n) (hj : Γ ⊢[PRAAx] lt j b) : Γ ⊢[PRAAx]
    entry (row f b x r) j ≐ Syn.subst ![r,j,x] f :=
  (sequence_decode (rowBody f) hj).eqTrans (row_body_at f x r j)
theorem row_congr (f : PTm 3) {b b' x x' r r' : PTm n}
    (hb : Γ ⊢[PRAAx] b ≐ b') (hx : Γ ⊢[PRAAx] x ≐ x') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    row f b x r ≐ row f b' x' r' := by
  simpa using Prf.eqCongr (Γ := Γ) (row f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![b,x,r]) (σ' := ![b',x',r']) (fun i => by fin_cases i; exact hb; exact hx; exact hr)
theorem table_body_at (f : PTm 3) (b x r : PTm n) : Γ ⊢[PRAAx]
    inst2 (tableBody f) r (pairT b x) ≐ row f b x r := by
  simp only [tableBody,inst2,subst_row,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact row_congr f (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
theorem table_length (f : PTm 3) (a b x : PTm n) : Γ ⊢[PRAAx] length (table f a b x) ≐ a := sequence_length _ _ _
theorem table_row (f : PTm 3) (a b x r : PTm n) (hr : Γ ⊢[PRAAx] lt r a) : Γ ⊢[PRAAx]
    entry (table f a b x) r ≐ row f b x r :=
  (sequence_decode (tableBody f) hr).eqTrans (table_body_at f b x r)
theorem table_row_length (f : PTm 3) (a b x r : PTm n) (hr : Γ ⊢[PRAAx] lt r a) : Γ ⊢[PRAAx]
    length (entry (table f a b x) r) ≐ b := (congrFst (table_row f a b x r hr)).eqTrans (row_length f b x r)
theorem table_lookup (f : PTm 3) (a b x r j : PTm n)
    (hr : Γ ⊢[PRAAx] lt r a) (hj : Γ ⊢[PRAAx] lt j b) : Γ ⊢[PRAAx]
    cell (table f a b x) r j ≐ Syn.subst ![r,j,x] f :=
  (entry_congr (table_row f a b x r hr) (.eqRefl _)).eqTrans (row_lookup f b x r j hj)

def powerBody : PTm 3 := power (entry (var 2) (var 0)) (var 1)
def U (R m : PTm n) : PTm n := table powerBody (length R) m R
def delta (r j : PTm n) : PTm n := RationalArithmetic.select (eqb r j) qzero qone
def weight (R r j : PTm n) : PTm n := RationalArithmetic.select
  (Signum.sg (PTm.monus (length R) r)) (delta r j) (power (entry R r) j)
def weightBody : PTm 3 := weight (var 2) (var 0) (var 1)
def W (R m : PTm n) : PTm n := table weightBody m m R
def constantBody : PTm 3 := singleton (weight (var 2) (var 0) (var 1))
def WP (R m : PTm n) : PTm n := table constantBody m m R

@[simp] theorem subst_U {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (U R m) = U (Syn.subst σ R) (Syn.subst σ m) := by simp [U]
@[simp] theorem subst_delta {l : ℕ} (σ : Fin n → PTm l) (r j : PTm n) :
    Syn.subst σ (delta r j) = delta (Syn.subst σ r) (Syn.subst σ j) := by simp [delta]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (R r j : PTm n) :
    Syn.subst σ (weight R r j) = weight (Syn.subst σ R) (Syn.subst σ r) (Syn.subst σ j) := by simp [weight]
@[simp] theorem subst_W {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (W R m) = W (Syn.subst σ R) (Syn.subst σ m) := by simp [W]
@[simp] theorem subst_WP {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (WP R m) = WP (Syn.subst σ R) (Syn.subst σ m) := by simp [WP]

theorem U_length (R m : PTm n) : Γ ⊢[PRAAx] length (U R m) ≐ length R := table_length _ _ _ _
theorem U_row_length (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    length (entry (U R m) r) ≐ m := table_row_length _ _ _ _ _ hr
theorem U_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (U R m) r j ≐ power (entry R r) j := by simpa [U,powerBody] using table_lookup powerBody (length R) m R r j hr hj
theorem U_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (U R m) r j) := GaussianRationalHorner.canonical_congr (U_lookup R m r j hr hj) (power_canonical _ _)
theorem delta_canonical (r j : PTm n) : Γ ⊢[PRAAx] canonical (delta r j) := by
  refine .orE (Foundations.BoundedReflection.eqb_cases r j) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (RationalArithmetic.select_zero _ _ _ Prf.hyp0) qzero_canonical
  · exact GaussianRationalHorner.canonical_congr (RationalArithmetic.select_one _ _ _ Prf.hyp0) qone_canonical
theorem weight_upper (R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    weight R r j ≐ power (entry R r) j := RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem weight_lower (R r j : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    weight R r j ≐ delta r j := RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hr)
theorem weight_canonical (R r j : PTm n) : Γ ⊢[PRAAx] canonical (weight R r j) := by
  refine .orE (lt_or_le r (length R)) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (weight_upper _ _ _ Prf.hyp0) (power_canonical _ _)
  · exact GaussianRationalHorner.canonical_congr (weight_lower _ _ _ Prf.hyp0) (delta_canonical _ _)
theorem W_length (R m : PTm n) : Γ ⊢[PRAAx] length (W R m) ≐ m := table_length _ _ _ _
theorem W_row_length (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (W R m) r) ≐ m := table_row_length _ _ _ _ _ hr
theorem W_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (W R m) r j ≐ weight R r j := by simpa [W,weightBody] using table_lookup weightBody m m R r j hr hj
theorem W_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (W R m) r j) := GaussianRationalHorner.canonical_congr (W_lookup R m r j hr hj) (weight_canonical _ _ _)
theorem WP_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (WP R m) r j ≐ singleton (weight R r j) := by simpa [WP,constantBody] using table_lookup constantBody m m R r j hr hj
theorem WP_cell_length (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell (WP R m) r j) ≐ one := (congrFst (WP_lookup R m r j hr hj)).eqTrans (singleton_length _)
theorem WP_coefficient (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (cell (WP R m) r j) zero ≐ weight R r j :=
  (entry_congr (WP_lookup R m r j hr hj) (.eqRefl _)).eqTrans (singleton_lookup _)
theorem WP_evaluation (R m r j z : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (WP R m) r j) z ≐ weight R r j :=
  (evaluate_congr (WP_lookup R m r j hr hj) (.eqRefl _)).eqTrans
    ((singleton_evaluation _ _).eqTrans (GaussianTranslatedNonconstant.recode_eq _ (weight_canonical _ _ _)))


/-- The five persistent fields are original scalar table, polynomial table,
degree bound, row and column. No evaluation point enters the producer. -/
def productData (S M L r j : PTm n) : PTm n := pairT S (pairT M (pairT L (pairT r j)))
def fields (x : PTm n) : Fin 5 → PTm n := ![fstT x,fstT (sndT x),
  fstT (sndT (sndT x)),fstT (sndT (sndT (sndT x))),sndT (sndT (sndT (sndT x)))]
def piece (S M r j t : PTm n) : PTm n := scaled (cell M t j) (cell S r t)
def initial : PTm 1 := zeros (succ (fields (var 0) 2))
def stepBody : PTm 3 := added (var 1)
  (piece (fields (var 2) 0) (fields (var 2) 1) (fields (var 2) 3) (fields (var 2) 4) (var 0))
  (succ (fields (var 2) 2))
def prefixF : PR 2 := rec2 initial stepBody
def partialProduct (S M L r j t : PTm n) : PTm n := ap2 prefixF t (productData S M L r j)
def productCell (S M m L r j : PTm n) : PTm n := partialProduct S M L r j m

@[simp] theorem subst_productData {l : ℕ} (σ : Fin n → PTm l) (S M L r j : PTm n) :
    Syn.subst σ (productData S M L r j) = productData (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ L) (Syn.subst σ r) (Syn.subst σ j) := by simp [productData]
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) (i : Fin 5) :
    Syn.subst σ (fields x i) = fields (Syn.subst σ x) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_piece {l : ℕ} (σ : Fin n → PTm l) (S M r j t : PTm n) :
    Syn.subst σ (piece S M r j t) = piece (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) := by simp [piece,cell]
@[simp] theorem subst_partialProduct {l : ℕ} (σ : Fin n → PTm l) (S M L r j t : PTm n) :
    Syn.subst σ (partialProduct S M L r j t) = partialProduct (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ L) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) := by simp [partialProduct]
@[simp] theorem subst_productCell {l : ℕ} (σ : Fin n → PTm l) (S M m L r j : PTm n) :
    Syn.subst σ (productCell S M m L r j) = productCell (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ r) (Syn.subst σ j) := by simp [productCell]

theorem field_at (S M L r j : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    fields (productData S M L r j) i ≐ ![S,M,L,r,j] i := by
  have e1 := snd_pair (Γ := Γ) S (pairT M (pairT L (pairT r j)))
  have e2 := (congrSnd e1).eqTrans (snd_pair M (pairT L (pairT r j)))
  have e3 := (congrSnd e2).eqTrans (snd_pair L (pairT r j))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrSnd e3).eqTrans (snd_pair _ _)
theorem piece_congr {S S' M M' r r' j j' t t' : PTm n}
    (hS : Γ ⊢[PRAAx] S ≐ S') (hM : Γ ⊢[PRAAx] M ≐ M') (hr : Γ ⊢[PRAAx] r ≐ r')
    (hj : Γ ⊢[PRAAx] j ≐ j') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    piece S M r j t ≐ piece S' M' r' j' t' := by
  simpa [piece] using Prf.eqCongr (Γ := Γ) (scaled (var 0) (var 1) : PTm 2)
    (σ := ![cell M t j,cell S r t]) (σ' := ![cell M' t' j',cell S' r' t']) (fun i => by
      fin_cases i
      · exact entry_congr (entry_congr hM ht) hj
      · exact entry_congr (entry_congr hS hr) ht)
theorem partial_congr {S S' M M' L L' r r' j j' t t' : PTm n}
    (hS : Γ ⊢[PRAAx] S ≐ S') (hM : Γ ⊢[PRAAx] M ≐ M') (hL : Γ ⊢[PRAAx] L ≐ L')
    (hr : Γ ⊢[PRAAx] r ≐ r') (hj : Γ ⊢[PRAAx] j ≐ j') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    partialProduct S M L r j t ≐ partialProduct S' M' L' r' j' t' :=
  congrAp2 prefixF ht (congrPairT hS (congrPairT hM (congrPairT hL (congrPairT hr hj))))
theorem prefix_zero (S M L r j : PTm n) : Γ ⊢[PRAAx]
    partialProduct S M L r j zero ≐ zeros (succ L) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (productData S M L r j)
  simp only [initial,GaussianRationalPolynomialBuffers.subst_zeros,ConciseIPRA.PTm.subst_succ,subst_fields,
    Syn.subst_var,Matrix.cons_val_zero] at e
  exact e.eqTrans (zeros_congr (congrSucc (field_at _ _ _ _ _ 2)))
theorem prefix_succ (S M L r j t : PTm n) : Γ ⊢[PRAAx]
    partialProduct S M L r j (succ t) ≐ added (partialProduct S M L r j t) (piece S M r j t) (succ L) := by
  have e := rec2_succ (Γ := Γ) initial stepBody t (productData S M L r j)
  simp only [stepBody,GaussianRationalPolynomialBuffers.subst_added,subst_piece,ConciseIPRA.PTm.subst_succ,
    subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  exact e.eqTrans (GaussianPolynomialDeterminant.added_congr (.eqRefl _)
    (piece_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 1)
      (field_at _ _ _ _ _ 3) (field_at _ _ _ _ _ 4) (.eqRefl _)) (congrSucc (field_at _ _ _ _ _ 2)))
theorem prefix_length (S M L r j t : PTm n) : Γ ⊢[PRAAx]
    length (partialProduct S M L r j t) ≐ succ L := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      (prefix_zero _ _ _ _ _))).eqTrans (zeros_length _)
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      (prefix_succ _ _ _ _ _ _))).eqTrans (added_length _ _ _)
theorem prefix_canonical (S M L r j t : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (partialProduct S M L r j t) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact canonical_coefficients_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      (prefix_zero _ _ _ _ _)) (zeros_canonical _)
  · exact canonical_coefficients_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      (prefix_succ _ _ _ _ _ _)) (added_canonical _ _ _)


def coefficientTerm (S M r j t s : PTm n) : PTm n := qmul (cell S r t) (entry (cell M t j) s)
def valueTerm (S M r j t z : PTm n) : PTm n := qmul (cell S r t) (evaluate (cell M t j) z)
def coefficientBody : PTm 2 := coefficientTerm (fields (var 1) 0) (fields (var 1) 1)
  (fields (var 1) 2) (fields (var 1) 3) (var 0) (fields (var 1) 4)
def valueBody : PTm 2 := valueTerm (fields (var 1) 0) (fields (var 1) 1)
  (fields (var 1) 2) (fields (var 1) 3) (var 0) (fields (var 1) 4)
def coefficientSum (S M r j t s : PTm n) : PTm n := GaussianRationalFiniteSum.sum coefficientBody t (productData S M r j s)
def valueSum (S M r j t z : PTm n) : PTm n := GaussianRationalFiniteSum.sum valueBody t (productData S M r j z)

@[simp] theorem subst_coefficientTerm {l : ℕ} (σ : Fin n → PTm l) (S M r j t s : PTm n) :
    Syn.subst σ (coefficientTerm S M r j t s) = coefficientTerm (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ s) := by simp [coefficientTerm,cell]
@[simp] theorem subst_valueTerm {l : ℕ} (σ : Fin n → PTm l) (S M r j t z : PTm n) :
    Syn.subst σ (valueTerm S M r j t z) = valueTerm (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ z) := by simp [valueTerm,cell]
@[simp] theorem subst_coefficientSum {l : ℕ} (σ : Fin n → PTm l) (S M r j t s : PTm n) :
    Syn.subst σ (coefficientSum S M r j t s) = coefficientSum (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ s) := by simp [coefficientSum]
@[simp] theorem subst_valueSum {l : ℕ} (σ : Fin n → PTm l) (S M r j t z : PTm n) :
    Syn.subst σ (valueSum S M r j t z) = valueSum (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ z) := by simp [valueSum]

theorem coefficient_body_at (S M r j t s : PTm n) : Γ ⊢[PRAAx]
    inst2 coefficientBody t (productData S M r j s) ≐ coefficientTerm S M r j t s := by
  simp only [coefficientBody,inst2,subst_coefficientTerm,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply qmul_congr
  · exact entry_congr (entry_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 2)) (.eqRefl _)
  · exact entry_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 1) (.eqRefl _))
      (field_at _ _ _ _ _ 3)) (field_at _ _ _ _ _ 4)
theorem value_body_at (S M r j t z : PTm n) : Γ ⊢[PRAAx]
    inst2 valueBody t (productData S M r j z) ≐ valueTerm S M r j t z := by
  simp only [valueBody,inst2,subst_valueTerm,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply qmul_congr
  · exact entry_congr (entry_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 2)) (.eqRefl _)
  · exact evaluate_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 1) (.eqRefl _))
      (field_at _ _ _ _ _ 3)) (field_at _ _ _ _ _ 4)
theorem coefficient_sum_zero (S M r j s : PTm n) : Γ ⊢[PRAAx]
    coefficientSum S M r j zero s ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem coefficient_sum_succ (S M r j t s : PTm n) : Γ ⊢[PRAAx]
    coefficientSum S M r j (succ t) s ≐ qadd (coefficientSum S M r j t s) (coefficientTerm S M r j t s) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (coefficient_body_at _ _ _ _ _ _))
theorem value_sum_zero (S M r j z : PTm n) : Γ ⊢[PRAAx]
    valueSum S M r j zero z ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem value_sum_succ (S M r j t z : PTm n) : Γ ⊢[PRAAx]
    valueSum S M r j (succ t) z ≐ qadd (valueSum S M r j t z) (valueTerm S M r j t z) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (value_body_at _ _ _ _ _ _))
theorem piece_length (S M m L r j t : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] lt t m) : Γ ⊢[PRAAx]
    length (piece S M r j t) ≐ succ L := (scaled_length _ _).eqTrans (cell_length M m L t j h ht hj)
theorem piece_coefficient (S M m L r j t s : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] lt t m) (hs : Γ ⊢[PRAAx] le s L) : Γ ⊢[PRAAx]
    entry (piece S M r j t) s ≐ coefficientTerm S M r j t s :=
  scaled_lookup _ _ _ (lt_congr (.eqRefl _) (cell_length M m L t j h ht hj).eqSymm
    ((succ_monus_succ _ _).eqTrans hs))
theorem piece_evaluation (S M r j t z : PTm n) : Γ ⊢[PRAAx]
    evaluate (piece S M r j t) z ≐ valueTerm S M r j t z := evaluation_linearity _ _ _

def coefficientLaw (S M m L r j s t : PTm n) : Fm PTm n := le t m ⟶
  entry (partialProduct S M L r j t) s ≐ coefficientSum S M r j t s
def valueLaw (S M m L r j z t : PTm n) : Fm PTm n := le t m ⟶
  evaluate (partialProduct S M L r j t) z ≐ valueSum S M r j t z
@[simp] theorem subst_coefficientLaw {l : ℕ} (σ : Fin n → PTm l) (S M m L r j s t : PTm n) :
    (coefficientLaw S M m L r j s t).subst σ = coefficientLaw (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ s) (Syn.subst σ t) := by simp [coefficientLaw]
@[simp] theorem subst_valueLaw {l : ℕ} (σ : Fin n → PTm l) (S M m L r j z t : PTm n) :
    (valueLaw S M m L r j z t).subst σ = valueLaw (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ t) := by simp [valueLaw]

theorem prefix_coefficient (S M m L r j t s : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] le t m) (hs : Γ ⊢[PRAAx] le s L) : Γ ⊢[PRAAx]
    entry (partialProduct S M L r j t) s ≐ coefficientSum S M r j t s := by
  have hsh : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using h.shift
  have hjsh : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have hssh : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift L) := by simpa only [Fm.shift,subst_le,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (coefficientLaw (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L)
      (Syn.shift r) (Syn.shift j) (Syn.shift s) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((entry_congr (prefix_zero _ _ _ _ _) (.eqRefl _)).eqTrans
        ((zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans (coefficient_sum_zero _ _ _ _ _).eqSymm))
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := coefficientLaw (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift r) (Syn.shift j) (Syn.shift s) (var 0)
      have ti : le (succ (var 0)) (Syn.shift m) :: I :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
      exact (entry_congr (prefix_succ _ _ _ _ _ _) (.eqRefl _)).eqTrans
        ((added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hssh.wk.wk)).eqTrans
          ((qadd_congr (.impE Prf.hyp1 (le_trans (le_succ_self _) ti))
            (piece_coefficient _ _ _ _ _ _ _ _ hsh.wk.wk hjsh.wk.wk ti hssh.wk.wk)).eqTrans
              (coefficient_sum_succ _ _ _ _ _ _).eqSymm))
  have law : Γ ⊢[PRAAx] coefficientLaw S M m L r j s t := by
    simpa only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE law ht

theorem prefix_evaluation (S M m L r j t z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    evaluate (partialProduct S M L r j t) z ≐ valueSum S M r j t z := by
  have hsh : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using h.shift
  have hjsh : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have all : Γ ⊢[PRAAx] .all (valueLaw (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L)
      (Syn.shift r) (Syn.shift j) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_valueLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((evaluate_congr (prefix_zero _ _ _ _ _) (.eqRefl _)).eqTrans
        ((zeros_evaluation _ _).eqTrans (value_sum_zero _ _ _ _ _).eqSymm))
    · simp only [subst_valueLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := valueLaw (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift r) (Syn.shift j) (Syn.shift z) (var 0)
      have ti : le (succ (var 0)) (Syn.shift m) :: I :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
      exact (evaluate_congr (prefix_succ _ _ _ _ _ _) (.eqRefl _)).eqTrans
        ((added_evaluation _ _ _ _ (prefix_length _ _ _ _ _ _) (piece_length _ _ _ _ _ _ _ hsh.wk.wk hjsh.wk.wk ti)).eqTrans
          ((qadd_congr (.impE Prf.hyp1 (le_trans (le_succ_self _) ti)) (piece_evaluation _ _ _ _ _ _)).eqTrans
            (value_sum_succ _ _ _ _ _ _).eqSymm))
  have law : Γ ⊢[PRAAx] valueLaw S M m L r j z t := by
    simpa only [subst_valueLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE law ht


def productBody : PTm 3 := productCell (fields (var 2) 0) (fields (var 2) 1)
  (fields (var 2) 2) (fields (var 2) 3) (var 0) (var 1)
def product (S M m L : PTm n) : PTm n := table productBody m m (productData S M m L zero)
def WM (R M m L : PTm n) : PTm n := product (W R m) M m L
@[simp] theorem subst_product {l : ℕ} (σ : Fin n → PTm l) (S M m L : PTm n) :
    Syn.subst σ (product S M m L) = product (Syn.subst σ S) (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by simp [product]
@[simp] theorem subst_WM {l : ℕ} (σ : Fin n → PTm l) (R M m L : PTm n) :
    Syn.subst σ (WM R M m L) = WM (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by simp [WM]

theorem product_length (S M m L : PTm n) : Γ ⊢[PRAAx] length (product S M m L) ≐ m := table_length _ _ _ _
theorem product_row_length (S M m L r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (product S M m L) r) ≐ m := table_row_length _ _ _ _ _ hr
theorem product_lookup (S M m L r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (product S M m L) r j ≐ productCell S M m L r j := by
  have e : Γ ⊢[PRAAx] cell (product S M m L) r j ≐ productCell
      (fields (productData S M m L zero) 0) (fields (productData S M m L zero) 1)
      (fields (productData S M m L zero) 2) (fields (productData S M m L zero) 3) r j := by
    simpa [product,productBody] using table_lookup productBody m m (productData S M m L zero) r j hr hj
  exact e.eqTrans (partial_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 1)
    (field_at _ _ _ _ _ 3) (.eqRefl _) (.eqRefl _) (field_at _ _ _ _ _ 2))
theorem product_cell_length (S M m L r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell (product S M m L) r j) ≐ succ L := (congrFst (product_lookup _ _ _ _ _ _ hr hj)).eqTrans (prefix_length _ _ _ _ _ _)
theorem product_canonical (S M m L r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonicalCoefficients (cell (product S M m L) r j) :=
  canonical_coefficients_congr (product_lookup _ _ _ _ _ _ hr hj) (prefix_canonical _ _ _ _ _ _)
theorem product_coefficient (S M m L r j s : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hs : Γ ⊢[PRAAx] le s L) : Γ ⊢[PRAAx]
    entry (cell (product S M m L) r j) s ≐ coefficientSum S M r j m s :=
  (entry_congr (product_lookup _ _ _ _ _ _ hr hj) (.eqRefl _)).eqTrans (prefix_coefficient _ _ _ _ _ _ _ _ h hj (le_refl _) hs)
theorem product_evaluation (S M m L r j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (product S M m L) r j) z ≐ valueSum S M r j m z :=
  (evaluate_congr (product_lookup _ _ _ _ _ _ hr hj) (.eqRefl _)).eqTrans (prefix_evaluation _ _ _ _ _ _ _ _ h hj (le_refl _))

theorem WP_row_cells (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] rowCells (WP R m) m zero r := by
  refine .allI (.impI ?_)
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  simpa only [cell,Syn.shift,subst_WP,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    WP_cell_length (Syn.shift R) (Syn.shift m) (Syn.shift r) (var 0) rs.wk Prf.hyp0
theorem WP_shape (R m : PTm n) : Γ ⊢[PRAAx] tableShape (WP R m) m zero := by
  refine .andI (table_length _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_WP,WP,subst_table] using table_row_length constantBody (Syn.shift m) (Syn.shift m) (Syn.shift R) (var 0) Prf.hyp0
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_WP,ConciseIPRA.PTm.subst_zero] using WP_row_cells (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0
theorem WP_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonicalCoefficients (cell (WP R m) r j) := by
  refine canonical_coefficients_congr (WP_lookup R m r j hr hj) (.allI (.impI ?_))
  have hl : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift (singleton (weight R r j))) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (singleton_length (Γ := Γ) (weight R r j)).shift
  have hlt := lt_congr (.eqRefl (var 0)) hl.wk (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift))
  have zi := (monus_zero _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans hlt)
  have e := (entry_congr (.eqRefl _) zi).eqTrans (singleton_lookup (weight (Syn.shift R) (Syn.shift r) (Syn.shift j)))
  simpa only [Syn.shift,GaussianRationalMonicReduction.subst_singleton,subst_weight] using
    GaussianRationalHorner.canonical_congr e (weight_canonical _ _ _)

theorem product_row_cells (S M m L r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    rowCells (product S M m L) m L r := by
  refine .allI (.impI ?_)
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  simpa only [cell,Syn.shift,subst_product,ConciseIPRA.PTm.subst_succ] using
    product_cell_length (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift r) (var 0) rs.wk Prf.hyp0
theorem product_shape (S M m L : PTm n) : Γ ⊢[PRAAx] tableShape (product S M m L) m L := by
  refine .andI (product_length _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_product] using product_row_length (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) Prf.hyp0
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_product] using product_row_cells (Syn.shift S) (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) Prf.hyp0

theorem value_sum_pairing (R M m r j z : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    valueSum (W R m) M r j m z ≐ GaussianPolynomialMultiplicationMatrix.pairing M m j z (entry R r) := by
  have rms : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hrm.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have e : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual valueBody GaussianPolynomialMultiplicationMatrix.pairingBody m
      (productData (W R m) M r j z) (GaussianPolynomialMultiplicationMatrix.pairingData M j z (entry R r)) := by
    refine .allI (.impI ?_)
    have e := (value_body_at (W (Syn.shift R) (Syn.shift m)) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift z)).eqTrans
      ((qmul_congr ((W_lookup _ _ _ _ rms.wk Prf.hyp0).eqTrans (weight_upper _ _ _ rs.wk)) (.eqRefl _)).eqTrans
        (GaussianPolynomialMultiplicationMatrix.pairing_body_at (Syn.shift M) (Syn.shift j) (Syn.shift z) (entry (Syn.shift R) (Syn.shift r)) (var 0)).eqSymm)
    simpa only [Syn.shift,subst_productData,subst_W,subst_entry,GaussianPolynomialMultiplicationMatrix.subst_pairingData] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ e).eqTrans
    (congrAp3 GaussianRationalHorner.hornerF (GaussianPolynomialMultiplicationMatrix.pairing_length M m j z (entry R r)).eqSymm (.eqRefl _) (.eqRefl _))
theorem upper_row_evaluation (R M m L r j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hrm : Γ ⊢[PRAAx] lt r m) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (WM R M m L) r j) z ≐ GaussianPolynomialMultiplicationMatrix.pairing M m j z (entry R r) :=
  (product_evaluation _ _ _ _ _ _ _ h hrm hj).eqTrans (value_sum_pairing _ _ _ _ _ _ hrm hr)



/-- The right-hand sides read the ACTUAL constant-polynomial table WP,
not a separately supplied scalar matrix-product interpretation. -/
def polynomialCoefficientTerm (S M r j t s : PTm n) : PTm n :=
  qmul (entry (cell S r t) zero) (entry (cell M t j) s)
def polynomialValueTerm (S M r j t z : PTm n) : PTm n :=
  qmul (evaluate (cell S r t) z) (evaluate (cell M t j) z)
def polynomialCoefficientBody : PTm 2 := polynomialCoefficientTerm (fields (var 1) 0) (fields (var 1) 1)
  (fields (var 1) 2) (fields (var 1) 3) (var 0) (fields (var 1) 4)
def polynomialValueBody : PTm 2 := polynomialValueTerm (fields (var 1) 0) (fields (var 1) 1)
  (fields (var 1) 2) (fields (var 1) 3) (var 0) (fields (var 1) 4)
def polynomialCoefficientSum (S M r j t s : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum polynomialCoefficientBody t (productData S M r j s)
def polynomialValueSum (S M r j t z : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum polynomialValueBody t (productData S M r j z)
@[simp] theorem subst_polynomialCoefficientTerm {l : ℕ} (σ : Fin n → PTm l) (S M r j t s : PTm n) :
    Syn.subst σ (polynomialCoefficientTerm S M r j t s) = polynomialCoefficientTerm (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ s) := by simp [polynomialCoefficientTerm,cell]
@[simp] theorem subst_polynomialValueTerm {l : ℕ} (σ : Fin n → PTm l) (S M r j t z : PTm n) :
    Syn.subst σ (polynomialValueTerm S M r j t z) = polynomialValueTerm (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ z) := by simp [polynomialValueTerm,cell]
@[simp] theorem subst_polynomialCoefficientSum {l : ℕ} (σ : Fin n → PTm l) (S M r j t s : PTm n) :
    Syn.subst σ (polynomialCoefficientSum S M r j t s) = polynomialCoefficientSum (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ s) := by simp [polynomialCoefficientSum]
@[simp] theorem subst_polynomialValueSum {l : ℕ} (σ : Fin n → PTm l) (S M r j t z : PTm n) :
    Syn.subst σ (polynomialValueSum S M r j t z) = polynomialValueSum (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ z) := by simp [polynomialValueSum]
theorem polynomial_coefficient_body_at (S M r j t s : PTm n) : Γ ⊢[PRAAx]
    inst2 polynomialCoefficientBody t (productData S M r j s) ≐ polynomialCoefficientTerm S M r j t s := by
  simp only [polynomialCoefficientBody,inst2,subst_polynomialCoefficientTerm,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply qmul_congr
  · exact entry_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 2)) (.eqRefl _)) (.eqRefl _)
  · exact entry_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 1) (.eqRefl _))
      (field_at _ _ _ _ _ 3)) (field_at _ _ _ _ _ 4)
theorem polynomial_value_body_at (S M r j t z : PTm n) : Γ ⊢[PRAAx]
    inst2 polynomialValueBody t (productData S M r j z) ≐ polynomialValueTerm S M r j t z := by
  simp only [polynomialValueBody,inst2,subst_polynomialValueTerm,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply qmul_congr
  · exact evaluate_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 2)) (.eqRefl _)) (field_at _ _ _ _ _ 4)
  · exact evaluate_congr (entry_congr (entry_congr (field_at _ _ _ _ _ 1) (.eqRefl _))
      (field_at _ _ _ _ _ 3)) (field_at _ _ _ _ _ 4)
theorem coefficient_sum_embedding (R M m r j s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    coefficientSum (W R m) M r j m s ≐ polynomialCoefficientSum (WP R m) M r j m s := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := (coefficient_body_at (W (Syn.shift R) (Syn.shift m)) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift s)).eqTrans
    ((qmul_congr ((W_lookup _ _ _ _ rs.wk Prf.hyp0).eqTrans (WP_coefficient _ _ _ _ rs.wk Prf.hyp0).eqSymm) (.eqRefl _)).eqTrans
      (polynomial_coefficient_body_at (WP (Syn.shift R) (Syn.shift m)) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift s)).eqSymm)
  simpa only [Syn.shift,subst_productData,subst_W,subst_WP] using e
theorem value_sum_embedding (R M m r j z : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    valueSum (W R m) M r j m z ≐ polynomialValueSum (WP R m) M r j m z := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := (value_body_at (W (Syn.shift R) (Syn.shift m)) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift z)).eqTrans
    ((qmul_congr ((W_lookup _ _ _ _ rs.wk Prf.hyp0).eqTrans (WP_evaluation _ _ _ _ (Syn.shift z) rs.wk Prf.hyp0).eqSymm) (.eqRefl _)).eqTrans
      (polynomial_value_body_at (WP (Syn.shift R) (Syn.shift m)) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift z)).eqSymm)
  simpa only [Syn.shift,subst_productData,subst_W,subst_WP] using e
theorem WM_coefficient (R M m L r j s : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hs : Γ ⊢[PRAAx] le s L) : Γ ⊢[PRAAx]
    entry (cell (WM R M m L) r j) s ≐ polynomialCoefficientSum (WP R m) M r j m s :=
  (product_coefficient _ _ _ _ _ _ _ h hr hj hs).eqTrans (coefficient_sum_embedding _ _ _ _ _ _ hr)
theorem WM_evaluation (R M m L r j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (WM R M m L) r j) z ≐ polynomialValueSum (WP R m) M r j m z :=
  (product_evaluation _ _ _ _ _ _ _ h hr hj).eqTrans (value_sum_embedding _ _ _ _ _ _ hr)

def scalarShape (T a b : PTm n) : Fm PTm n := (length T ≐ a) ⋏ .all
  (lt (var 0) (Syn.shift a) ⟶ length (entry (Syn.shift T) (var 0)) ≐ Syn.shift b)
@[simp] theorem subst_scalarShape {l : ℕ} (σ : Fin n → PTm l) (T a b : PTm n) :
    (scalarShape T a b).subst σ = scalarShape (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [scalarShape,Syn.subst_shift,Syn.shift_subst]
theorem U_shape (R m : PTm n) : Γ ⊢[PRAAx] scalarShape (U R m) (length R) m := by
  refine .andI (U_length _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_U,subst_length] using U_row_length (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0
theorem W_shape (R m : PTm n) : Γ ⊢[PRAAx] scalarShape (W R m) m m := by
  refine .andI (W_length _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_W] using W_row_length (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0

theorem table_shape_congr {M M' m L : PTm n} (e : Γ ⊢[PRAAx] M ≐ M')
    (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx] tableShape M' m L := by
  simpa only [GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (tableShape (var 0) (var 1) (var 2) : Fm PTm 3)
      ![M,m,L] ![M',m,L] (fun i => by fin_cases i; exact e; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.subst_var,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h)


/-- Bind precisely the polynomial matrix returned by the existing norm
program, without asserting equality of arbitrary outer table encodings. -/
def sourceMatrix (F G m a c : PTm n) : PTm n := fstT (sndT (GaussianPolynomialMonicNorm.run F G m a c))
def sourceProduct (F G m a c L p g : PTm n) : PTm n := WM (GaussianRationalCurveFibers.yList L p g)
  (sourceMatrix F G m a c) m (GaussianPolynomialMonicNorm.width m a c)
@[simp] theorem subst_sourceMatrix {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (sourceMatrix F G m a c) = sourceMatrix (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [sourceMatrix]
@[simp] theorem subst_sourceProduct {l : ℕ} (σ : Fin n → PTm l) (F G m a c L p g : PTm n) :
    Syn.subst σ (sourceProduct F G m a c L p g) = sourceProduct (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [sourceProduct]

theorem source_matrix_shape (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) : Γ ⊢[PRAAx]
    tableShape (sourceMatrix F G m a c) m (GaussianPolynomialMonicNorm.width m a c) :=
  table_shape_congr (GaussianPolynomialMonicNorm.returned_matrix _ _ _ _ _).eqSymm
    (GaussianPolynomialMonicNorm.multiplication_table_shape _ _ _ _ _ (.andE₁ h) (.andE₂ (.andE₂ h)))
theorem source_product_shape (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    tableShape (sourceProduct F G m a c L p g) m (GaussianPolynomialMonicNorm.width m a c) := product_shape _ _ _ _
theorem source_fiber_bound (F G m L p g : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L) : Γ ⊢[PRAAx]
    le (length (GaussianRationalCurveFibers.yList L p g)) m :=
  le_congr (GaussianRationalCurveFibers.y_length L p g).eqSymm (.eqRefl _)
    (GaussianRationalCurveFibers.fiber_size_bound F m L p g (.andE₁ (.andE₂ h)) (.andE₁ h))

theorem source_zero_row_at (F G m a c L p g r j : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hr : Γ ⊢[PRAAx] lt r (GaussianRationalFiberGrouping.fiberCount L p g))
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (sourceProduct F G m a c L p g) r j) (GaussianRationalCurveFibers.selectedX L p g) ≐ qzero := by
  have rt : Γ ⊢[PRAAx] lt r (length (GaussianRationalCurveFibers.yList L p g)) :=
    lt_congr (.eqRefl _) (GaussianRationalCurveFibers.y_length L p g).eqSymm hr
  have rm := le_trans rt (source_fiber_bound F G m L p g hPoints)
  exact (upper_row_evaluation _ _ _ _ _ _ _ (source_matrix_shape F G m a c hNorm) rm rt hj).eqTrans
    (GaussianPolynomialMonicNorm.returned_zero_action F G m a c j (GaussianRationalCurveFibers.selectedX L p g)
      (entry (GaussianRationalCurveFibers.yList L p g) r) hNorm hj
      (GaussianRationalCurveFibers.curve_root_at F m L p g r (.andE₁ (.andE₂ hPoints)) hr)
      (GaussianRationalCurveFibers.function_root_at G m L p g r (.andE₂ (.andE₂ hPoints)) hr))

def firstRowsZero (P m t x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift t) ⟶ .all (lt (var 0) (Syn.shift (Syn.shift m)) ⟶
    evaluate (cell (Syn.shift (Syn.shift P)) (var 1) (var 0)) (Syn.shift (Syn.shift x)) ≐ qzero))
@[simp] theorem subst_firstRowsZero {l : ℕ} (σ : Fin n → PTm l) (P m t x : PTm n) :
    (firstRowsZero P m t x).subst σ = firstRowsZero (Syn.subst σ P) (Syn.subst σ m) (Syn.subst σ t) (Syn.subst σ x) := by
  simp [firstRowsZero,cell,Syn.subst_shift,Syn.shift_subst]
theorem source_zero_rows (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L) : Γ ⊢[PRAAx]
    firstRowsZero (sourceProduct F G m a c L p g) m (GaussianRationalFiberGrouping.fiberCount L p g)
      (GaussianRationalCurveFibers.selectedX L p g) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) ::
    List.map Fm.shift (lt (var 0) (Syn.shift (GaussianRationalFiberGrouping.fiberCount L p g)) :: Γ.map Fm.shift)
  have ns : Δ ⊢[PRAAx] GaussianPolynomialMonicNorm.input (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift G))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift c)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianPolynomialMonicNorm.subst_input,Syn.shift] using hNorm.shift.shift.wk.wk
  have ps : Δ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift G))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift L)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianRationalCurveFibers.subst_sourceInput,Syn.shift] using hPoints.shift.shift.wk.wk

  have rh0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift (GaussianRationalFiberGrouping.fiberCount L p g))).shift := Prf.hyp1
  have e := source_zero_row_at (Syn.shift (Syn.shift F)) (Syn.shift (Syn.shift G)) (Syn.shift (Syn.shift m))
    (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift p)) (Syn.shift (Syn.shift g))
    (var 1) (var 0) ns ps
    (by simpa only [Fm.shift,subst_lt,Foundations.FiniteFiberGrouping.subst_fiberCount,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rh0) Prf.hyp0
  simpa only [Δ,Syn.shift,subst_sourceProduct,GaussianRationalCurveFibers.subst_selectedX] using e


theorem W_upper (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hr : Γ ⊢[PRAAx] lt r (length R))
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] cell (W R m) r j ≐ power (entry R r) j :=
  (W_lookup _ _ _ _ hrm hj).eqTrans (weight_upper _ _ _ hr)
theorem W_lower (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hr : Γ ⊢[PRAAx] le (length R) r)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] cell (W R m) r j ≐ delta r j :=
  (W_lookup _ _ _ _ hrm hj).eqTrans (weight_lower _ _ _ hr)

/-- All source data are original numerical inputs. The selected fiber size
and the vanishing rows are conclusions, not an incoming output contract. -/
def certificate (F G m a c L p g : PTm n) : Fm PTm n :=
  scalarShape (U (GaussianRationalCurveFibers.yList L p g) m) (length (GaussianRationalCurveFibers.yList L p g)) m ⋏
  (scalarShape (W (GaussianRationalCurveFibers.yList L p g) m) m m ⋏
  (tableShape (WP (GaussianRationalCurveFibers.yList L p g) m) m zero ⋏
  (tableShape (sourceProduct F G m a c L p g) m (GaussianPolynomialMonicNorm.width m a c) ⋏
  ((length (GaussianRationalCurveFibers.yList L p g) ≐ GaussianRationalFiberGrouping.fiberCount L p g) ⋏
  (le one (GaussianRationalFiberGrouping.fiberCount L p g) ⋏
  (le (GaussianRationalFiberGrouping.fiberCount L p g) m ⋏
  (firstRowsZero (sourceProduct F G m a c L p g) m (GaussianRationalFiberGrouping.fiberCount L p g)
    (GaussianRationalCurveFibers.selectedX L p g) ⋏
  (GaussianRationalFiberGrouping.partitionTotal L p ≐ length L))))))))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (F G m a c L p g : PTm n) :
    (certificate F G m a c L p g).subst σ = certificate (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by
  simp [certificate]
theorem fiber_vandermonde (F G m a c L p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hg : Γ ⊢[PRAAx] lt g (GaussianRationalFiberGrouping.groupCount L p)) : Γ ⊢[PRAAx]
    certificate F G m a c L p g :=
  .andI (U_shape _ _) (.andI (W_shape _ _) (.andI (WP_shape _ _) (.andI (source_product_shape _ _ _ _ _ _ _ _)
    (.andI (GaussianRationalCurveFibers.y_length _ _ _) (.andI (GaussianRationalFiberGrouping.fiber_nonempty _ _ _ hg)
      (.andI (GaussianRationalCurveFibers.fiber_size_bound _ _ _ _ _ (.andE₁ (.andE₂ hPoints)) (.andE₁ hPoints))
        (.andI (source_zero_rows _ _ _ _ _ _ _ _ hNorm hPoints) (GaussianRationalFiberGrouping.cardinal_partition _ _))))))))

def output (F G m a c L p g : PTm n) : PTm n :=
  pairT (pairT (U (GaussianRationalCurveFibers.yList L p g) m)
    (pairT (W (GaussianRationalCurveFibers.yList L p g) m)
      (pairT (WP (GaussianRationalCurveFibers.yList L p g) m) (sourceProduct F G m a c L p g))))
    (pairT (GaussianRationalCurveFibers.yList L p g) (pairT (GaussianRationalFiberGrouping.fiberCount L p g)
      (pairT (GaussianRationalCurveFibers.selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p))))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (F G m a c L p g : PTm n) : PTm n := app outputF ![F,G,m,a,c,L,p,g]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F G m a c L p g : PTm n) :
    Syn.subst σ (output F G m a c L p g) = output (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (F G m a c L p g : PTm n) :
    Syn.subst σ (run F G m a c L p g) = run (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (F G m a c L p g : PTm n) : Γ ⊢[PRAAx] run F G m a c L p g ≐ output F G m a c L p g := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![F,G,m,a,c,L,p,g]
theorem returned_tables (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (run F G m a c L p g) ≐ pairT (U (GaussianRationalCurveFibers.yList L p g) m)
      (pairT (W (GaussianRationalCurveFibers.yList L p g) m)
        (pairT (WP (GaussianRationalCurveFibers.yList L p g) m) (sourceProduct F G m a c L p g))) :=
  (congrFst (program_at _ _ _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_data (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (run F G m a c L p g) ≐ pairT (GaussianRationalCurveFibers.yList L p g)
      (pairT (GaussianRationalFiberGrouping.fiberCount L p g)
        (pairT (GaussianRationalCurveFibers.selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p))) :=
  (congrSnd (program_at _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_U (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (fstT (run F G m a c L p g)) ≐ U (GaussianRationalCurveFibers.yList L p g) m :=
  (congrFst (returned_tables _ _ _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_W (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (fstT (run F G m a c L p g))) ≐ W (GaussianRationalCurveFibers.yList L p g) m :=
  (congrFst ((congrSnd (returned_tables _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_WP (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (fstT (run F G m a c L p g)))) ≐ WP (GaussianRationalCurveFibers.yList L p g) m :=
  (congrFst ((congrSnd ((congrSnd (returned_tables _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_WM (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (fstT (run F G m a c L p g)))) ≐ sourceProduct F G m a c L p g :=
  (congrSnd ((congrSnd ((congrSnd (returned_tables _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_R (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F G m a c L p g)) ≐ GaussianRationalCurveFibers.yList L p g :=
  (congrFst (returned_data _ _ _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_t (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run F G m a c L p g))) ≐ GaussianRationalFiberGrouping.fiberCount L p g :=
  (congrFst ((congrSnd (returned_data _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_x (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run F G m a c L p g)))) ≐ GaussianRationalCurveFibers.selectedX L p g :=
  (congrFst ((congrSnd ((congrSnd (returned_data _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_partition (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run F G m a c L p g)))) ≐ GaussianRationalFiberGrouping.partitionTotal L p :=
  (congrSnd ((congrSnd ((congrSnd (returned_data _ _ _ _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_cardinal_partition (F G m a c L p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run F G m a c L p g)))) ≐ length L :=
  (returned_partition _ _ _ _ _ _ _ _).eqTrans (GaussianRationalFiberGrouping.cardinal_partition _ _)
theorem returned_zero_row (F G m a c L p g r j : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m L)
    (hr : Γ ⊢[PRAAx] lt r (GaussianRationalFiberGrouping.fiberCount L p g))
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (sndT (sndT (sndT (fstT (run F G m a c L p g))))) r j)
      (fstT (sndT (sndT (sndT (run F G m a c L p g))))) ≐ qzero :=
  (evaluate_congr (entry_congr (entry_congr (returned_WM _ _ _ _ _ _ _ _) (.eqRefl _)) (.eqRefl _))
    (returned_x _ _ _ _ _ _ _ _)).eqTrans (source_zero_row_at _ _ _ _ _ _ _ _ _ _ hNorm hPoints hr hj)

/-! Closed endpoints bind every dimension, source code and row index in
ordinary PRA proofs. The generic shape guards concern original cells only. -/
theorem power_tables_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarShape (U (var 0) (var 1)) (length (var 0)) (var 1) ⋏
      (scalarShape (W (var 0) (var 1)) (var 1) (var 1) ⋏ tableShape (WP (var 0) (var 1)) (var 1) zero)) :=
  closeUniv 2 (.andI (U_shape _ _) (.andI (W_shape _ _) (WP_shape _ _)))
theorem actual_polynomial_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (tableShape (var 1) (var 2) (var 3) ⟶ lt (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      evaluate (cell (product (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)) (var 6) ≐
        valueSum (var 0) (var 1) (var 4) (var 5) (var 2) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (product_evaluation _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_polynomial_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (tableShape (var 1) (var 2) (var 3) ⟶ lt (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶ le (var 6) (var 3) ⟶
      entry (cell (product (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)) (var 6) ≐
        coefficientSum (var 0) (var 1) (var 4) (var 5) (var 2) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (product_coefficient _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_WP_matrix_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (tableShape (var 1) (var 2) (var 3) ⟶ lt (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      evaluate (cell (WM (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)) (var 6) ≐
        polynomialValueSum (WP (var 0) (var 2)) (var 1) (var 4) (var 5) (var 2) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (WM_evaluation _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem original_fiber_vandermonde_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalCurveFibers.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      lt (var 7) (GaussianRationalFiberGrouping.groupCount (var 5) (var 6)) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (fiber_vandermonde _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem fiber_vandermonde_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ⋏
      (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))) ≐ length (var 5))) :=
  closeUniv 8 (.andI (program_at _ _ _ _ _ _ _ _) (returned_cardinal_partition _ _ _ _ _ _ _ _))
theorem returned_fiber_zero_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalCurveFibers.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      lt (var 8) (GaussianRationalFiberGrouping.fiberCount (var 5) (var 6) (var 7)) ⟶ lt (var 9) (var 2) ⟶
      evaluate (cell (sndT (sndT (sndT (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) (var 8) (var 9))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) ≐ qzero) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (returned_zero_row _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde
