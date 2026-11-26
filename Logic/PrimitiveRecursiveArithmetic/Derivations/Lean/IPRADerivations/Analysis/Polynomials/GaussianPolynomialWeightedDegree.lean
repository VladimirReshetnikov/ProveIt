import IPRADerivations.Analysis.Polynomials.GaussianPolynomialMonicNorm
import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialDegree
import IPRADerivations.Foundations.WeightedMonomials
import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual tagged weighted-degree maximum of the original coefficient rows

The source coefficient of Y^i is read from the SAME descending original
row list at slot m i. Computed field-nonzero tags exclude zero rows from
the actual numerical maximum scan. A nonzero row of weight zero has score
one and therefore still beats every zero row. Original finite nonzero
coefficient evidence derives a selected nonzero maximum; actual coprime
weight arithmetic derives its uniqueness. No determinant degree or
matrix-specialization law is assumed or asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialWeightedDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot slot_range)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (G m i : PTm n) : PTm n := entry G (slot m i)
def rowFlag (G m a i : PTm n) : PTm n := GaussianRationalPolynomialDegree.flag (row G m i) a
def rowDegree (G m a i : PTm n) : PTm n := GaussianRationalPolynomialDegree.degree (row G m i) a
def rowFirst (G m a i : PTm n) : PTm n := GaussianRationalPolynomialDegree.first (row G m i) a
def rowLeading (G m a i : PTm n) : PTm n := recode (entry (row G m i) (rowFirst G m a i))
def weight (G m a d i : PTm n) : PTm n := m*rowDegree G m a i+d*i
def score (G m a d i : PTm n) : PTm n := rowFlag G m a i*succ (weight G m a d i)
def data (G m a d : PTm n) : PTm n := pairT G (pairT m (pairT a d))
def fields (p : PTm n) : Fin 4 → PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
def scoreBody : PTm 2 := score (fields (var 1) 0) (fields (var 1) 1)
  (fields (var 1) 2) (fields (var 1) 3) (var 0)
def maximumPrefix (G m a d j : PTm n) : PTm n := Probability.UnionUtility.Mx scoreBody j (data G m a d)
def index (G m a d : PTm n) : PTm n := Probability.UnionUtility.Ag scoreBody m (data G m a d)
def weightedDegree (G m a d : PTm n) : PTm n := pred (maximumPrefix G m a d m)
def flag (G m a d : PTm n) : PTm n := Signum.sg (maximumPrefix G m a d m)
def nonzeroRows (G m a : PTm n) : Fm PTm n := .ex (lt (var 0) (Syn.shift m) ⋏
  GaussianRationalPolynomialDegree.nonzeroCoefficients (row (Syn.shift G) (Syn.shift m) (var 0)) (Syn.shift a))
def input (G m a : PTm n) : Fm PTm n := le one m ⋏ (rowShape G m a ⋏ nonzeroRows G m a)

@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (G m i : PTm n) :
    Syn.subst σ (row G m i) = row (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ i) := by simp [row]
@[simp] theorem subst_rowFlag {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowFlag G m a i) = rowFlag (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowFlag]
@[simp] theorem subst_rowDegree {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowDegree G m a i) = rowDegree (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowDegree]
@[simp] theorem subst_rowFirst {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowFirst G m a i) = rowFirst (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowFirst]
@[simp] theorem subst_rowLeading {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowLeading G m a i) = rowLeading (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowLeading]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (G m a d i : PTm n) :
    Syn.subst σ (weight G m a d i) = weight (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ i) := by simp [weight]
@[simp] theorem subst_score {l : ℕ} (σ : Fin n → PTm l) (G m a d i : PTm n) :
    Syn.subst σ (score G m a d i) = score (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ i) := by simp [score]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (data G m a d) = data (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_maximumPrefix {l : ℕ} (σ : Fin n → PTm l) (G m a d j : PTm n) :
    Syn.subst σ (maximumPrefix G m a d j) = maximumPrefix (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ j) := by simp [maximumPrefix]
@[simp] theorem subst_index {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (index G m a d) = index (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [index]
@[simp] theorem subst_weightedDegree {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (weightedDegree G m a d) = weightedDegree (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [weightedDegree]
@[simp] theorem subst_flag {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (flag G m a d) = flag (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [flag,Signum.sg]
@[simp] theorem subst_nonzeroRows {l : ℕ} (σ : Fin n → PTm l) (G m a : PTm n) :
    (nonzeroRows G m a).subst σ = nonzeroRows (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) := by
  simp [nonzeroRows,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (G m a : PTm n) :
    (input G m a).subst σ = input (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) := by simp [input]

theorem fields_at (G m a d : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] fields (data G m a d) i ≐ ![G,m,a,d] i := by
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  · exact (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
  · exact (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem score_body_at (G m a d i : PTm n) : Γ ⊢[PRAAx]
    inst2 scoreBody i (data G m a d) ≐ score G m a d i := by
  simp only [scoreBody,inst2,subst_score,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_score,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (score (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fields (data G m a d) 0,fields (data G m a d) 1,fields (data G m a d) 2,fields (data G m a d) 3,i])
      (σ' := ![G,m,a,d,i]) (fun j => by
        fin_cases j
        · exact fields_at _ _ _ _ 0
        · exact fields_at _ _ _ _ 1
        · exact fields_at _ _ _ _ 2
        · exact fields_at _ _ _ _ 3
        · exact .eqRefl _)

theorem row_length (G m a i : PTm n) (h : Γ ⊢[PRAAx] rowShape G m a)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] length (row G m i) ≐ succ a :=
  row_shape_at _ _ _ _ h (slot_range _ _ hi)
theorem row_degree_bound (G m a i : PTm n) : Γ ⊢[PRAAx] le (rowDegree G m a i) a :=
  GaussianRationalPolynomialDegree.degree_le _ _
theorem score_zero (G m a d i : PTm n) (h : Γ ⊢[PRAAx] rowFlag G m a i ≐ zero) : Γ ⊢[PRAAx]
    score G m a d i ≐ zero := (congrMul h (.eqRefl _)).eqTrans (zero_mul _)
theorem score_one (G m a d i : PTm n) (h : Γ ⊢[PRAAx] rowFlag G m a i ≐ one) : Γ ⊢[PRAAx]
    score G m a d i ≐ succ (weight G m a d i) := (congrMul h (.eqRefl _)).eqTrans (one_mul _)
theorem prefix_zero (G m a d : PTm n) : Γ ⊢[PRAAx] maximumPrefix G m a d zero ≐ zero := Probability.UnionUtility.mx_zero _ _
theorem prefix_succ (G m a d j : PTm n) : Γ ⊢[PRAAx]
    maximumPrefix G m a d (succ j) ≐ Foundations.DemandClosure.maximum (maximumPrefix G m a d j) (score G m a d j) :=
  (Probability.UnionUtility.mx_succ _ _ _).eqTrans
    (congrAdd (.eqRefl _) (congrMonus (score_body_at _ _ _ _ _) (.eqRefl _)))
theorem prefix_upper (G m a d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    le (score G m a d i) (maximumPrefix G m a d m) :=
  le_congr (score_body_at _ _ _ _ _) (.eqRefl _) (Probability.UnionUtility.mx_upper scoreBody hi)

theorem index_attains (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    lt (index G m a d) m ⋏ (score G m a d (index G m a d) ≐ maximumPrefix G m a d m) := by
  have form := RationalIntegerNormalization.positive_form hm
  have ai := congrAp2 (Probability.UnionUtility.agF scoreBody) form (.eqRefl (data G m a d))
  have mx := congrAp2 (Probability.UnionUtility.mxF scoreBody) form (.eqRefl (data G m a d))
  have h := Probability.UnionUtility.ag_attains (Γ := Γ) scoreBody (pred m) (data G m a d)
  exact .andI (lt_congr ai.eqSymm form.eqSymm (.andE₁ h))
    ((score_body_at _ _ _ _ _).eqSymm.eqTrans
      ((congrInst2 scoreBody ai (.eqRefl _)).eqTrans ((Prf.andE₂ h).eqTrans mx.eqSymm)))

theorem prefix_positive_from_row (G m a d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m)
    (h : Γ ⊢[PRAAx] rowFlag G m a i ≐ one) : Γ ⊢[PRAAx] le one (maximumPrefix G m a d m) :=
  le_trans (le_congr (.eqRefl _) (score_one _ _ _ _ _ h).eqSymm
    (le_of_eq_add (d := weight G m a d i) (by ipra_ring))) (prefix_upper _ _ _ _ _ hi)
theorem prefix_positive (G m a d : PTm n) (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    le one (maximumPrefix G m a d m) := by
  refine .exE h ?_
  let Δ := (lt (var 0) (Syn.shift m) ⋏ GaussianRationalPolynomialDegree.nonzeroCoefficients
    (row (Syn.shift G) (Syn.shift m) (var 0)) (Syn.shift a)) :: Γ.map Fm.shift
  have pos : Δ ⊢[PRAAx] le one (maximumPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift m)) :=
    prefix_positive_from_row (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0)
    (.andE₁ Prf.hyp0) (GaussianRationalPolynomialDegree.flag_one_of_nonzero _ _ (.andE₂ Prf.hyp0))
  simpa only [Δ,Fm.shift,subst_le,subst_maximumPrefix,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using pos

theorem selected_flag_of_positive (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hp : Γ ⊢[PRAAx] le one (maximumPrefix G m a d m)) : Γ ⊢[PRAAx]
    rowFlag G m a (index G m a d) ≐ one := by
  refine .orE (GaussianRationalPolynomialDegree.flag_cases (row G m (index G m a d)) a) ?_ Prf.hyp0
  have eq : (rowFlag G m a (index G m a d) ≐ zero) :: Γ ⊢[PRAAx] maximumPrefix G m a d m ≐ zero :=
    (Prf.andE₂ (index_attains _ _ _ _ hm)).wk.eqSymm.eqTrans (score_zero _ _ _ _ _ Prf.hyp0)
  exact not_succ_le_self zero _ (le_congr (.eqRefl _) eq hp.wk)

theorem selected_flag_one (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx] rowFlag G m a (index G m a d) ≐ one :=
  selected_flag_of_positive _ _ _ _ hm (prefix_positive _ _ _ _ h)
theorem maximum_eq_weight (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    weightedDegree G m a d ≐ weight G m a d (index G m a d) :=
  (congrPred ((Prf.andE₂ (index_attains _ _ _ _ hm)).eqSymm.eqTrans
    (score_one _ _ _ _ _ (selected_flag_one _ _ _ _ hm h)))).eqTrans (pred_succ _)
theorem leading_canonical (G m a i : PTm n) : Γ ⊢[PRAAx] canonical (rowLeading G m a i) := recode_canonical _
theorem leading_nonzero (G m a i : PTm n) (h : Γ ⊢[PRAAx] rowFlag G m a i ≐ one) : Γ ⊢[PRAAx]
    neg (rowLeading G m a i ≐ qzero) :=
  GaussianRationalPolynomialDegree.first_nonzero _ _ (GaussianRationalPolynomialDegree.found_of_flag_one _ _ h)
theorem selected_leading_nonzero (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    neg (rowLeading G m a (index G m a d) ≐ qzero) := leading_nonzero _ _ _ _ (selected_flag_one _ _ _ _ hm h)

theorem weight_le_max (G m a d i : PTm n) (h : Γ ⊢[PRAAx] nonzeroRows G m a)
    (hi : Γ ⊢[PRAAx] lt i m) (hRow : Γ ⊢[PRAAx] rowFlag G m a i ≐ one) : Γ ⊢[PRAAx]
    le (weight G m a d i) (weightedDegree G m a d) :=
  (succ_monus_succ _ _).eqSymm.eqTrans
    (le_congr (score_one _ _ _ _ _ hRow)
      (RationalIntegerNormalization.positive_form (prefix_positive _ _ _ _ h)) (prefix_upper _ _ _ _ _ hi))
theorem weighted_degree_bound (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    le (weightedDegree G m a d) (m*a+d*pred m) := by
  have bound := add_le_add₂
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl m) (row_degree_bound G m a (index G m a d)))
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl d)
      (GaussianPolynomialMultiplicationMatrix.index_le_pred m (index G m a d) hm (.andE₁ (index_attains _ _ _ _ hm))))
  exact le_congr (maximum_eq_weight _ _ _ _ hm h).eqSymm (.eqRefl _) bound

theorem equal_weight_indices (G m a d i j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m)
    (h : Γ ⊢[PRAAx] weight G m a d i ≐ weight G m a d j) : Γ ⊢[PRAAx] i ≐ j :=
  .andE₁ (Foundations.WeightedMonomials.weight_unique (RationalIntegerNormalization.positive_form hm) hg hi hj h)
theorem unique_max (G m a d i : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (h : Γ ⊢[PRAAx] nonzeroRows G m a)
    (hi : Γ ⊢[PRAAx] lt i m) (hEq : Γ ⊢[PRAAx] weight G m a d i ≐ weightedDegree G m a d) : Γ ⊢[PRAAx]
    i ≐ index G m a d := equal_weight_indices _ _ _ _ _ _ hm hg hi (.andE₁ (index_attains _ _ _ _ hm))
      (hEq.eqTrans (maximum_eq_weight _ _ _ _ hm h))
theorem strict_below (G m a d i : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (h : Γ ⊢[PRAAx] nonzeroRows G m a)
    (hi : Γ ⊢[PRAAx] lt i m) (hRow : Γ ⊢[PRAAx] rowFlag G m a i ≐ one)
    (hne : Γ ⊢[PRAAx] neg (i ≐ index G m a d)) : Γ ⊢[PRAAx]
    lt (weight G m a d i) (weightedDegree G m a d) := by
  refine .orE (lt_or_eq_of_le (weight_le_max _ _ _ _ _ h hi hRow)) Prf.hyp0 ?_
  exact .botE _ (.impE hne.wk (unique_max _ _ _ _ _ hm.wk hg.wk h.wk hi.wk Prf.hyp0))

theorem flag_one_of_positive (G m a d : PTm n) (hp : Γ ⊢[PRAAx] le one (maximumPrefix G m a d m)) : Γ ⊢[PRAAx]
    flag G m a d ≐ one :=
  (Probability.UnionUtility.congrSg' (RationalIntegerNormalization.positive_form hp)).eqTrans (Signum.sg_succ _)
theorem flag_one_of_nonzero (G m a d : PTm n) (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    flag G m a d ≐ one := flag_one_of_positive _ _ _ _ (prefix_positive _ _ _ _ h)
theorem positive_of_flag_one (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ one) : Γ ⊢[PRAAx]
    le one (maximumPrefix G m a d m) := by
  refine .orE (zero_or_succ (maximumPrefix G m a d m)) ?_ ?_
  · exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans
      ((Probability.UnionUtility.congrSg' Prf.hyp0).eqTrans Signum.sg_zero)))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_of_eq_add (d := pred (maximumPrefix G m a d m)) (by ipra_ring))
theorem zero_count_flag (G a d : PTm n) : Γ ⊢[PRAAx] flag G zero a d ≐ zero :=
  (Probability.UnionUtility.congrSg' (prefix_zero G zero a d)).eqTrans Signum.sg_zero
theorem positive_count_of_flag_one (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ one) : Γ ⊢[PRAAx]
    le one m := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have e : (m ≐ zero) :: Γ ⊢[PRAAx] flag G m a d ≐ flag G zero a d := by
      ipra_congr (flag (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl G, Prf.hyp0, .eqRefl a, .eqRefl d]
    exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (e.eqTrans (zero_count_flag _ _ _))))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_of_eq_add (d := pred m) (by ipra_ring))
theorem nonzero_of_flag_one (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ one) : Γ ⊢[PRAAx]
    nonzeroRows G m a := by
  have hm := positive_count_of_flag_one _ _ _ _ h
  have hp := positive_of_flag_one _ _ _ _ h
  refine .exI (index G m a d) ?_
  simpa only [Fm.subst_and,subst_lt,GaussianRationalPolynomialDegree.subst_nonzeroCoefficients,
    subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.andI (Prf.andE₁ (index_attains _ _ _ _ hm))
      (GaussianRationalPolynomialDegree.nonzero_of_flag_one _ _ (selected_flag_of_positive _ _ _ _ hm hp))
theorem flag_iff_nonzero_rows (G m a d : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag G m a d ≐ one) (nonzeroRows G m a) :=
  .andI (.impI (nonzero_of_flag_one _ _ _ _ Prf.hyp0)) (.impI (flag_one_of_nonzero _ _ _ _ Prf.hyp0))

theorem flag_cases (G m a d : PTm n) : Γ ⊢[PRAAx] (flag G m a d ≐ zero) ⋎ (flag G m a d ≐ one) :=
  .orE (zero_or_succ (maximumPrefix G m a d m))
    (.orI₁ ((Probability.UnionUtility.congrSg' Prf.hyp0).eqTrans Signum.sg_zero))
    (.orI₂ ((Probability.UnionUtility.congrSg' Prf.hyp0).eqTrans (Signum.sg_succ _)))
theorem prefix_zero_of_failure (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ zero) : Γ ⊢[PRAAx]
    maximumPrefix G m a d m ≐ zero := by
  refine .orE (zero_or_succ (maximumPrefix G m a d m)) Prf.hyp0 ?_
  have oneEq : (maximumPrefix G m a d m ≐ succ (pred (maximumPrefix G m a d m))) :: Γ ⊢[PRAAx]
      flag G m a d ≐ one := (Probability.UnionUtility.congrSg' Prf.hyp0).eqTrans (Signum.sg_succ _)
  exact .botE _ (succ_ne_zero (oneEq.eqSymm.eqTrans h.wk))
theorem weighted_degree_zero_of_failure (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ zero) : Γ ⊢[PRAAx]
    weightedDegree G m a d ≐ zero := (congrPred (prefix_zero_of_failure _ _ _ _ h)).eqTrans pred_zero
theorem failure_no_nonzero_rows (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ zero) : Γ ⊢[PRAAx]
    neg (nonzeroRows G m a) := .impI (succ_ne_zero ((flag_one_of_nonzero _ _ _ _ Prf.hyp0).eqSymm.eqTrans h.wk))
theorem zero_count_index (G a d : PTm n) : Γ ⊢[PRAAx] index G zero a d ≐ zero := Probability.UnionUtility.ag_zero _ _
theorem zero_count_weight (G a d : PTm n) : Γ ⊢[PRAAx] weightedDegree G zero a d ≐ zero :=
  weighted_degree_zero_of_failure _ _ _ _ (zero_count_flag _ _ _)

def certificate (G m a d : PTm n) : Fm PTm n := lt (index G m a d) m ⋏
  ((flag G m a d ≐ one) ⋏ ((rowFlag G m a (index G m a d) ≐ one) ⋏
    ((length (row G m (index G m a d)) ≐ succ a) ⋏
      ((weightedDegree G m a d ≐ weight G m a d (index G m a d)) ⋏
        (canonical (rowLeading G m a (index G m a d)) ⋏
          (neg (rowLeading G m a (index G m a d) ≐ qzero) ⋏ le (weightedDegree G m a d) (m*a+d*pred m)))))))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    (certificate G m a d).subst σ = certificate (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [certificate]
theorem maximum_correct (G m a d : PTm n) (h : Γ ⊢[PRAAx] input G m a) : Γ ⊢[PRAAx] certificate G m a d := by
  have hm := Prf.andE₁ h
  have hn := Prf.andE₂ (Prf.andE₂ h)
  have hb := Prf.andE₁ (index_attains G m a d hm)
  exact .andI hb (.andI (flag_one_of_nonzero _ _ _ _ hn)
    (.andI (selected_flag_one _ _ _ _ hm hn) (.andI (row_length _ _ _ _ (.andE₁ (.andE₂ h)) hb)
      (.andI (maximum_eq_weight _ _ _ _ hm hn) (.andI (leading_canonical _ _ _ _)
        (.andI (selected_leading_nonzero _ _ _ _ hm hn) (weighted_degree_bound _ _ _ _ hm hn)))))))

/-- The actual source tag, ascending Y index, numerical weight and original row leading value. -/
def output (G m a d : PTm n) : PTm n := pairT (flag G m a d)
  (pairT (index G m a d) (pairT (weightedDegree G m a d) (rowLeading G m a (index G m a d))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (G m a d : PTm n) : PTm n := app outputF ![G,m,a,d]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (output G m a d) = output (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (run G m a d) = run (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [run]
  funext i
  fin_cases i <;> rfl
theorem program_at (G m a d : PTm n) : Γ ⊢[PRAAx] run G m a d ≐ output G m a d := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![G,m,a,d]
theorem returned_flag (G m a d : PTm n) : Γ ⊢[PRAAx] fstT (run G m a d) ≐ flag G m a d :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_index (G m a d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run G m a d)) ≐ index G m a d :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_weight (G m a d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run G m a d))) ≐ weightedDegree G m a d :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_leading (G m a d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run G m a d))) ≐ rowLeading G m a (index G m a d) :=
  (congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_flag_one (G m a d : PTm n) (h : Γ ⊢[PRAAx] input G m a) : Γ ⊢[PRAAx] fstT (run G m a d) ≐ one :=
  (returned_flag _ _ _ _).eqTrans (flag_one_of_nonzero _ _ _ _ (.andE₂ (.andE₂ h)))
theorem returned_index_bound (G m a d : PTm n) (h : Γ ⊢[PRAAx] input G m a) : Γ ⊢[PRAAx] lt (fstT (sndT (run G m a d))) m :=
  lt_congr (returned_index _ _ _ _).eqSymm (.eqRefl _) (.andE₁ (index_attains _ _ _ _ (.andE₁ h)))
theorem returned_leading_canonical (G m a d : PTm n) : Γ ⊢[PRAAx] canonical (sndT (sndT (sndT (run G m a d)))) :=
  GaussianRationalHorner.canonical_congr (returned_leading _ _ _ _) (leading_canonical _ _ _ _)
theorem returned_leading_nonzero (G m a d : PTm n) (h : Γ ⊢[PRAAx] input G m a) : Γ ⊢[PRAAx]
    neg (sndT (sndT (sndT (run G m a d))) ≐ qzero) := .impI
  (.impE (selected_leading_nonzero _ _ _ _ (.andE₁ h) (.andE₂ (.andE₂ h))).wk
    ((returned_leading _ _ _ _).wk.eqSymm.eqTrans Prf.hyp0))

theorem original_row_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowShape (var 0) (var 1) (var 2) ⟶ lt (var 3) (var 1) ⟶ length (row (var 0) (var 1) (var 3)) ≐ succ (var 2)) :=
  closeUniv 4 (.impI (.impI (row_length _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_weighted_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (maximum_correct _ _ _ _ Prf.hyp0))
theorem actual_tagged_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (flag (var 0) (var 1) (var 2) (var 3) ≐ one) (nonzeroRows (var 0) (var 1) (var 2))) :=
  closeUniv 4 (flag_iff_nonzero_rows _ _ _ _)
theorem actual_failure_sentinel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (flag (var 0) (var 1) (var 2) (var 3) ≐ zero ⟶
      ((weightedDegree (var 0) (var 1) (var 2) (var 3) ≐ zero) ⋏ neg (nonzeroRows (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.andI (weighted_degree_zero_of_failure _ _ _ _ Prf.hyp0) (failure_no_nonzero_rows _ _ _ _ Prf.hyp0)))
theorem actual_empty_scan_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((flag (var 0) zero (var 1) (var 2) ≐ zero) ⋏
      ((index (var 0) zero (var 1) (var 2) ≐ zero) ⋏ weightedDegree (var 0) zero (var 1) (var 2) ≐ zero)) :=
  closeUniv 3 (.andI (zero_count_flag _ _ _) (.andI (zero_count_index _ _ _) (zero_count_weight _ _ _)))
theorem actual_maximality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) ⟶ lt (var 4) (var 1) ⟶ rowFlag (var 0) (var 1) (var 2) (var 4) ≐ one ⟶
      le (weight (var 0) (var 1) (var 2) (var 3) (var 4)) (weightedDegree (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (weight_le_max _ _ _ _ _ (.andE₂ (.andE₂ Prf.hyp1.wk)) Prf.hyp1 Prf.hyp0))))
theorem actual_coprime_unique_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) ⟶ gcd (var 1) (var 3) ≐ one ⟶ lt (var 4) (var 1) ⟶
      weight (var 0) (var 1) (var 2) (var 3) (var 4) ≐ weightedDegree (var 0) (var 1) (var 2) (var 3) ⟶
        var 4 ≐ index (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (unique_max _ _ _ _ _ (.andE₁ Prf.hyp1.wk.wk) Prf.hyp1.wk
      (.andE₂ (.andE₂ Prf.hyp1.wk.wk)) Prf.hyp1 Prf.hyp0)))))
theorem actual_strict_other_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) ⟶ gcd (var 1) (var 3) ≐ one ⟶ lt (var 4) (var 1) ⟶
      rowFlag (var 0) (var 1) (var 2) (var 4) ≐ one ⟶ neg (var 4 ≐ index (var 0) (var 1) (var 2) (var 3)) ⟶
        lt (weight (var 0) (var 1) (var 2) (var 3) (var 4)) (weightedDegree (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (strict_below _ _ _ _ _ (.andE₁ Prf.hyp1.wk.wk.wk) Prf.hyp1.wk.wk
      (.andE₂ (.andE₂ Prf.hyp1.wk.wk.wk)) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_weighted_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶
      ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ one) ⋏
        (lt (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (var 1) ⋏
          neg (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ qzero)))) :=
  closeUniv 4 (.impI (.andI (returned_flag_one _ _ _ _ Prf.hyp0)
    (.andI (returned_index_bound _ _ _ _ Prf.hyp0) (returned_leading_nonzero _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialWeightedDegree
