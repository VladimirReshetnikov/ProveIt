import IPRADerivations.Analysis.Polynomials.RationalPolynomialNonvanishing
import IPRADerivations.Analysis.Polynomials.Elimination.RationalBivariateGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialWeightedDegree

/-!
# The original rational tagged weighted-degree scan

Original descending rational rows are tested for nonzero field values by the
actual rational scan. Their tagged scores feed the actual finite maximum and
argmax recursors. Genuine guarded QF induction identifies both prefix scans
with the Gaussian computation on the actual embedded declared row prefixes.
No supplied maximum, degree, scan or outer-code equality law is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialWeightedDegreeGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open GaussianPolynomialMultiplicationMatrix (slot slot_range)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def embedded (G m a : PTm n) : PTm n := RationalRowSpanGaussianEmbedding.matrix G m (succ a)
def row (G m i : PTm n) : PTm n := entry G (slot m i)
def rowFlag (G m a i : PTm n) : PTm n := RationalPolynomialDegreeGaussianEmbedding.flag (row G m i) a
def rowDegree (G m a i : PTm n) : PTm n := RationalPolynomialDegreeGaussianEmbedding.degree (row G m i) a
def weight (G m a d i : PTm n) : PTm n := m*rowDegree G m a i+d*i
def score (G m a d i : PTm n) : PTm n := rowFlag G m a i*succ (weight G m a d i)
def data (G m a d : PTm n) : PTm n := GaussianPolynomialWeightedDegree.data G m a d
def scoreBody : PTm 2 := score (GaussianPolynomialWeightedDegree.fields (var 1) 0)
  (GaussianPolynomialWeightedDegree.fields (var 1) 1) (GaussianPolynomialWeightedDegree.fields (var 1) 2)
  (GaussianPolynomialWeightedDegree.fields (var 1) 3) (var 0)
def maximumPrefix (G m a d j : PTm n) : PTm n := Probability.UnionUtility.Mx scoreBody j (data G m a d)
def indexPrefix (G m a d j : PTm n) : PTm n := Probability.UnionUtility.Ag scoreBody j (data G m a d)
def targetIndexPrefix (G m a d j : PTm n) : PTm n := Probability.UnionUtility.Ag GaussianPolynomialWeightedDegree.scoreBody j
  (GaussianPolynomialWeightedDegree.data (embedded G m a) m a d)
def index (G m a d : PTm n) : PTm n := indexPrefix G m a d m
def weightedDegree (G m a d : PTm n) : PTm n := pred (maximumPrefix G m a d m)
def flag (G m a d : PTm n) : PTm n := Signum.sg (maximumPrefix G m a d m)
def nonzeroRows (G m a : PTm n) : Fm PTm n := .ex (lt (var 0) (Syn.shift m) ⋏
  RationalPolynomialNonvanishing.nonzeroCoefficients (row (Syn.shift G) (Syn.shift m) (var 0)) (Syn.shift a))

@[simp] theorem subst_embedded {l : ℕ} (σ : Fin n → PTm l) (G m a : PTm n) :
    Syn.subst σ (embedded G m a) = embedded (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) := by simp [embedded]
@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (G m i : PTm n) :
    Syn.subst σ (row G m i) = row (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ i) := by simp [row]
@[simp] theorem subst_rowFlag {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowFlag G m a i) = rowFlag (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowFlag]
@[simp] theorem subst_rowDegree {l : ℕ} (σ : Fin n → PTm l) (G m a i : PTm n) :
    Syn.subst σ (rowDegree G m a i) = rowDegree (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ i) := by simp [rowDegree]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (G m a d i : PTm n) :
    Syn.subst σ (weight G m a d i) = weight (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ i) := by simp [weight]
@[simp] theorem subst_score {l : ℕ} (σ : Fin n → PTm l) (G m a d i : PTm n) :
    Syn.subst σ (score G m a d i) = score (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ i) := by simp [score]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (data G m a d) = data (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_maximumPrefix {l : ℕ} (σ : Fin n → PTm l) (G m a d j : PTm n) :
    Syn.subst σ (maximumPrefix G m a d j) = maximumPrefix (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ j) := by simp [maximumPrefix]
@[simp] theorem subst_indexPrefix {l : ℕ} (σ : Fin n → PTm l) (G m a d j : PTm n) :
    Syn.subst σ (indexPrefix G m a d j) = indexPrefix (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ j) := by simp [indexPrefix]
@[simp] theorem subst_targetIndexPrefix {l : ℕ} (σ : Fin n → PTm l) (G m a d j : PTm n) :
    Syn.subst σ (targetIndexPrefix G m a d j) = targetIndexPrefix (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ j) := by simp [targetIndexPrefix]
@[simp] theorem subst_index {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (index G m a d) = index (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [index]
@[simp] theorem subst_weightedDegree {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (weightedDegree G m a d) = weightedDegree (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [weightedDegree]
@[simp] theorem subst_flag {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (flag G m a d) = flag (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [flag,Signum.sg]
@[simp] theorem subst_nonzeroRows {l : ℕ} (σ : Fin n → PTm l) (G m a : PTm n) :
    (nonzeroRows G m a).subst σ = nonzeroRows (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) := by
  simp [nonzeroRows,Syn.subst_shift,Syn.shift_subst]

theorem row_flag_conjugacy (G m a i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    rowFlag G m a i ≐ GaussianPolynomialWeightedDegree.rowFlag (embedded G m a) m a i :=
  RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy _ _ a
    (RationalBivariateGaussianEmbedding.row_embedding G m (succ a) (slot m i) (slot_range m i hi))
theorem row_degree_conjugacy (G m a i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    rowDegree G m a i ≐ GaussianPolynomialWeightedDegree.rowDegree (embedded G m a) m a i :=
  RationalPolynomialDegreeGaussianEmbedding.degree_conjugacy _ _ a
    (RationalBivariateGaussianEmbedding.row_embedding G m (succ a) (slot m i) (slot_range m i hi))
theorem weight_conjugacy (G m a d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    weight G m a d i ≐ GaussianPolynomialWeightedDegree.weight (embedded G m a) m a d i :=
  congrAdd (congrMul (.eqRefl _) (row_degree_conjugacy G m a i hi)) (.eqRefl _)
theorem score_conjugacy (G m a d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    score G m a d i ≐ GaussianPolynomialWeightedDegree.score (embedded G m a) m a d i :=
  congrMul (row_flag_conjugacy G m a i hi) (congrSucc (weight_conjugacy G m a d i hi))

theorem score_body_at (G m a d i : PTm n) : Γ ⊢[PRAAx] inst2 scoreBody i (data G m a d) ≐ score G m a d i := by
  simp only [scoreBody,inst2,subst_score,GaussianPolynomialWeightedDegree.subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_score,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (score (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![GaussianPolynomialWeightedDegree.fields (data G m a d) 0,GaussianPolynomialWeightedDegree.fields (data G m a d) 1,
        GaussianPolynomialWeightedDegree.fields (data G m a d) 2,GaussianPolynomialWeightedDegree.fields (data G m a d) 3,i])
      (σ' := ![G,m,a,d,i]) (fun j => by
        fin_cases j
        · exact GaussianPolynomialWeightedDegree.fields_at _ _ _ _ 0
        · exact GaussianPolynomialWeightedDegree.fields_at _ _ _ _ 1
        · exact GaussianPolynomialWeightedDegree.fields_at _ _ _ _ 2
        · exact GaussianPolynomialWeightedDegree.fields_at _ _ _ _ 3
        · exact .eqRefl _)

theorem prefix_zero (G m a d : PTm n) : Γ ⊢[PRAAx] maximumPrefix G m a d zero ≐ zero := Probability.UnionUtility.mx_zero _ _
theorem index_prefix_zero (G m a d : PTm n) : Γ ⊢[PRAAx] indexPrefix G m a d zero ≐ zero := Probability.UnionUtility.ag_zero _ _
theorem prefix_succ (G m a d j : PTm n) : Γ ⊢[PRAAx] maximumPrefix G m a d (succ j) ≐
    maximumPrefix G m a d j+LeanProofs.IPRA.PTm.monus (score G m a d j) (maximumPrefix G m a d j) :=
  (Probability.UnionUtility.mx_succ _ _ _).eqTrans
    (congrAdd (.eqRefl _) (congrMonus (score_body_at _ _ _ _ _) (.eqRefl _)))
theorem index_prefix_succ (G m a d j : PTm n) : Γ ⊢[PRAAx] indexPrefix G m a d (succ j) ≐
    indexPrefix G m a d j+Signum.sg (LeanProofs.IPRA.PTm.monus (score G m a d j) (maximumPrefix G m a d j))*
      LeanProofs.IPRA.PTm.monus j (indexPrefix G m a d j) :=
  (Probability.UnionUtility.ag_succ _ _ _).eqTrans
    (congrAdd (.eqRefl _) (congrMul (Probability.UnionUtility.congrSg' (congrMonus (score_body_at _ _ _ _ _) (.eqRefl _))) (.eqRefl _)))
theorem target_index_prefix_succ (G m a d j : PTm n) : Γ ⊢[PRAAx] targetIndexPrefix G m a d (succ j) ≐
    targetIndexPrefix G m a d j+Signum.sg (LeanProofs.IPRA.PTm.monus (GaussianPolynomialWeightedDegree.score (embedded G m a) m a d j)
      (GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d j))*LeanProofs.IPRA.PTm.monus j (targetIndexPrefix G m a d j) :=
  (Probability.UnionUtility.ag_succ _ _ _).eqTrans
    (congrAdd (.eqRefl _) (congrMul (Probability.UnionUtility.congrSg'
      (congrMonus (GaussianPolynomialWeightedDegree.score_body_at _ _ _ _ _) (.eqRefl _))) (.eqRefl _)))

def prefixLaw (G m a d j : PTm n) : Fm PTm n := le j m ⟶
  (maximumPrefix G m a d j ≐ GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d j ⋏
    indexPrefix G m a d j ≐ targetIndexPrefix G m a d j)
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (G m a d j : PTm n) :
    (prefixLaw G m a d j).subst σ = prefixLaw (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ j) := by simp [prefixLaw]

theorem prefix_step (G m a d j : PTm n) (hj : Γ ⊢[PRAAx] lt j m)
    (ih : Γ ⊢[PRAAx] maximumPrefix G m a d j ≐ GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d j ⋏
      indexPrefix G m a d j ≐ targetIndexPrefix G m a d j) : Γ ⊢[PRAAx]
    maximumPrefix G m a d (succ j) ≐ GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d (succ j) ⋏
      indexPrefix G m a d (succ j) ≐ targetIndexPrefix G m a d (succ j) := by
  have hmax : Γ ⊢[PRAAx] maximumPrefix G m a d j ≐ GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d j := .andE₁ ih
  have hindex : Γ ⊢[PRAAx] indexPrefix G m a d j ≐ targetIndexPrefix G m a d j := .andE₂ ih
  have hscore := score_conjugacy G m a d j hj
  exact .andI ((prefix_succ _ _ _ _ _).eqTrans
    ((congrAdd hmax (congrMonus hscore hmax)).eqTrans (GaussianPolynomialWeightedDegree.prefix_succ _ _ _ _ _).eqSymm))
    ((index_prefix_succ _ _ _ _ _).eqTrans
      ((congrAdd hindex (congrMul (Probability.UnionUtility.congrSg' (congrMonus hscore hmax)) (congrMonus (.eqRefl _) hindex))).eqTrans
        (target_index_prefix_succ _ _ _ _ _).eqSymm))

theorem prefix_conjugacy (G m a d j : PTm n) (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    maximumPrefix G m a d j ≐ GaussianPolynomialWeightedDegree.maximumPrefix (embedded G m a) m a d j ⋏
      indexPrefix G m a d j ≐ targetIndexPrefix G m a d j := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (.andI ((prefix_zero G m a d).eqTrans (GaussianPolynomialWeightedDegree.prefix_zero _ _ _ _).eqSymm)
        ((index_prefix_zero G m a d).eqTrans (Probability.UnionUtility.ag_zero _ _).eqSymm))
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_step _ _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw G m a d j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem weighted_degree_conjugacy (G m a d : PTm n) : Γ ⊢[PRAAx]
    weightedDegree G m a d ≐ GaussianPolynomialWeightedDegree.weightedDegree (embedded G m a) m a d :=
  congrPred (.andE₁ (prefix_conjugacy G m a d m (le_refl _)))
theorem index_conjugacy (G m a d : PTm n) : Γ ⊢[PRAAx]
    index G m a d ≐ GaussianPolynomialWeightedDegree.index (embedded G m a) m a d :=
  .andE₂ (prefix_conjugacy G m a d m (le_refl _))
theorem flag_conjugacy (G m a d : PTm n) : Γ ⊢[PRAAx]
    flag G m a d ≐ GaussianPolynomialWeightedDegree.flag (embedded G m a) m a d :=
  Probability.UnionUtility.congrSg' (.andE₁ (prefix_conjugacy G m a d m (le_refl _)))

theorem row_nonzero_iff (G m a i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] Fm.iff
    (RationalPolynomialNonvanishing.nonzeroCoefficients (row G m i) a)
    (GaussianRationalPolynomialDegree.nonzeroCoefficients (GaussianPolynomialWeightedDegree.row (embedded G m a) m i) a) := by
  have eq := row_flag_conjugacy G m a i hi
  exact .andI (.impI (GaussianRationalPolynomialDegree.nonzero_of_flag_one _ _
    (eq.wk.eqSymm.eqTrans (RationalPolynomialNonvanishing.flag_of_nonzero _ _ Prf.hyp0))))
    (.impI (RationalPolynomialNonvanishing.nonzero_of_flag _ _
      (eq.wk.eqTrans (GaussianRationalPolynomialDegree.flag_one_of_nonzero _ _ Prf.hyp0))))

theorem nonzero_rows_to_gaussian (G m a : PTm n) (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.nonzeroRows (embedded G m a) m a := by
  refine .exE h ?_
  let E := lt (var 0) (Syn.shift m) ⋏ RationalPolynomialNonvanishing.nonzeroCoefficients
    (row (Syn.shift G) (Syn.shift m) (var 0)) (Syn.shift a)
  let Δ := E :: Γ.map Fm.shift
  have found : Δ ⊢[PRAAx] E := Prf.hyp0
  have nonzero := (row_nonzero_iff (Syn.shift G) (Syn.shift m) (Syn.shift a) (var 0) (.andE₁ found)).iffMp (.andE₂ found)
  have result : Δ ⊢[PRAAx] GaussianPolynomialWeightedDegree.nonzeroRows
      (embedded (Syn.shift G) (Syn.shift m) (Syn.shift a)) (Syn.shift m) (Syn.shift a) := by
    refine .exI (var 0) ?_
    simpa [GaussianPolynomialWeightedDegree.nonzeroRows] using Prf.andI (.andE₁ found) nonzero
  simpa [Δ,E,Fm.shift,Syn.shift] using result

theorem nonzero_rows_from_gaussian (G m a : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.nonzeroRows (embedded G m a) m a) : Γ ⊢[PRAAx] nonzeroRows G m a := by
  refine .exE h ?_
  let E := lt (var 0) (Syn.shift m) ⋏ GaussianRationalPolynomialDegree.nonzeroCoefficients
    (GaussianPolynomialWeightedDegree.row (embedded (Syn.shift G) (Syn.shift m) (Syn.shift a)) (Syn.shift m) (var 0)) (Syn.shift a)
  let Δ := E :: Γ.map Fm.shift
  have found : Δ ⊢[PRAAx] E := Prf.hyp0
  have nonzero := (row_nonzero_iff (Syn.shift G) (Syn.shift m) (Syn.shift a) (var 0) (.andE₁ found)).iffMpr (.andE₂ found)
  have result : Δ ⊢[PRAAx] nonzeroRows (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    refine .exI (var 0) ?_
    simpa [nonzeroRows] using Prf.andI (.andE₁ found) nonzero
  simpa [Δ,E,Fm.shift,Syn.shift] using result

theorem nonzero_rows_iff (G m a : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (nonzeroRows G m a) (GaussianPolynomialWeightedDegree.nonzeroRows (embedded G m a) m a) :=
  .andI (.impI (nonzero_rows_to_gaussian _ _ _ Prf.hyp0)) (.impI (nonzero_rows_from_gaussian _ _ _ Prf.hyp0))

theorem target_input (G m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] nonzeroRows G m a) :
    Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input (embedded G m a) m a :=
  .andI hm (.andI (RationalBivariateGaussianEmbedding.embedded_row_shape G m a) (nonzero_rows_to_gaussian G m a h))

theorem flag_one_of_nonzero (G m a d : PTm n) (h : Γ ⊢[PRAAx] nonzeroRows G m a) : Γ ⊢[PRAAx] flag G m a d ≐ one :=
  (flag_conjugacy G m a d).eqTrans (GaussianPolynomialWeightedDegree.flag_one_of_nonzero _ _ _ _ (nonzero_rows_to_gaussian G m a h))
theorem nonzero_of_flag_one (G m a d : PTm n) (h : Γ ⊢[PRAAx] flag G m a d ≐ one) : Γ ⊢[PRAAx] nonzeroRows G m a :=
  nonzero_rows_from_gaussian G m a (GaussianPolynomialWeightedDegree.nonzero_of_flag_one _ _ _ _
    ((flag_conjugacy G m a d).eqSymm.eqTrans h))
theorem flag_iff_nonzero_rows (G m a d : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag G m a d ≐ one) (nonzeroRows G m a) :=
  .andI (.impI (nonzero_of_flag_one _ _ _ _ Prf.hyp0)) (.impI (flag_one_of_nonzero _ _ _ _ Prf.hyp0))

theorem index_bound (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] lt (index G m a d) m :=
  lt_congr (index_conjugacy G m a d).eqSymm (.eqRefl _) (.andE₁ (GaussianPolynomialWeightedDegree.index_attains _ _ _ _ hm))
theorem weighted_degree_bound (G m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] nonzeroRows G m a) :
    Γ ⊢[PRAAx] le (weightedDegree G m a d) (m*a+d*pred m) :=
  le_congr (weighted_degree_conjugacy G m a d).eqSymm (.eqRefl _)
    (GaussianPolynomialWeightedDegree.weighted_degree_bound _ _ _ _ hm (nonzero_rows_to_gaussian G m a h))

theorem zero_count (G a d : PTm n) : Γ ⊢[PRAAx]
    flag G zero a d ≐ zero ⋏ (index G zero a d ≐ zero ⋏ weightedDegree G zero a d ≐ zero) :=
  .andI ((flag_conjugacy G zero a d).eqTrans (GaussianPolynomialWeightedDegree.zero_count_flag _ _ _))
    (.andI ((index_conjugacy G zero a d).eqTrans (GaussianPolynomialWeightedDegree.zero_count_index _ _ _))
      ((weighted_degree_conjugacy G zero a d).eqTrans (GaussianPolynomialWeightedDegree.zero_count_weight _ _ _)))

def output (G m a d : PTm n) : PTm n := pairT (flag G m a d) (pairT (index G m a d) (weightedDegree G m a d))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (G m a d : PTm n) : PTm n := PTm.app outputF ![G,m,a,d]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (output G m a d) = output (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (G m a d : PTm n) :
    Syn.subst σ (run G m a d) = run (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (G m a d : PTm n) : Γ ⊢[PRAAx] run G m a d ≐ output G m a d := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![G,m,a,d]
theorem returned_flag (G m a d : PTm n) : Γ ⊢[PRAAx] fstT (run G m a d) ≐ flag G m a d :=
  (congrFst (program_at G m a d)).eqTrans (fst_pair _ _)
theorem returned_index (G m a d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run G m a d)) ≐ index G m a d :=
  (congrFst ((congrSnd (program_at G m a d)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_degree (G m a d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run G m a d)) ≐ weightedDegree G m a d :=
  (congrSnd ((congrSnd (program_at G m a d)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_gaussian_degree (G m a d : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run G m a d)) ≐ GaussianPolynomialWeightedDegree.weightedDegree (embedded G m a) m a d :=
  (returned_degree G m a d).eqTrans (weighted_degree_conjugacy G m a d)

theorem actual_rational_weighted_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶
      (maximumPrefix (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        GaussianPolynomialWeightedDegree.maximumPrefix (embedded (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3) (var 4) ⋏
        indexPrefix (var 0) (var 1) (var 2) (var 3) (var 4) ≐ targetIndexPrefix (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (prefix_conjugacy _ _ _ _ _ Prf.hyp0))

theorem actual_rational_weighted_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (weightedDegree (var 0) (var 1) (var 2) (var 3) ≐
      GaussianPolynomialWeightedDegree.weightedDegree (embedded (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (weighted_degree_conjugacy _ _ _ _)
theorem actual_rational_weighted_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((flag (var 0) (var 1) (var 2) (var 3) ≐ GaussianPolynomialWeightedDegree.flag (embedded (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) ⋏
      index (var 0) (var 1) (var 2) (var 3) ≐ GaussianPolynomialWeightedDegree.index (embedded (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.andI (flag_conjugacy _ _ _ _) (index_conjugacy _ _ _ _))

theorem actual_rational_nonzero_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (nonzeroRows (var 0) (var 1) (var 2))
      (GaussianPolynomialWeightedDegree.nonzeroRows (embedded (var 0) (var 1) (var 2)) (var 1) (var 2))) :=
  closeUniv 3 (nonzero_rows_iff _ _ _)
theorem actual_rational_weighted_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (flag (var 0) (var 1) (var 2) (var 3) ≐ one) (nonzeroRows (var 0) (var 1) (var 2))) :=
  closeUniv 4 (flag_iff_nonzero_rows _ _ _ _)

theorem actual_rational_weighted_target_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ nonzeroRows (var 0) (var 1) (var 2) ⟶
      GaussianPolynomialWeightedDegree.input (embedded (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (target_input _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_weighted_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ nonzeroRows (var 0) (var 1) (var 2) ⟶
      (lt (index (var 0) (var 1) (var 2) (var 3)) (var 1) ⋏
        le (weightedDegree (var 0) (var 1) (var 2) (var 3)) (var 1*var 2+var 3*pred (var 1)))) :=
  closeUniv 4 (.impI (.impI (.andI (index_bound _ _ _ _ Prf.hyp1) (weighted_degree_bound _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_rational_empty_weighted_scan_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (flag (var 0) zero (var 1) (var 2) ≐ zero ⋏
      (index (var 0) zero (var 1) (var 2) ≐ zero ⋏ weightedDegree (var 0) zero (var 1) (var 2) ≐ zero)) :=
  closeUniv 3 (zero_count _ _ _)
theorem actual_rational_weighted_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_rational_weighted_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐
      GaussianPolynomialWeightedDegree.weightedDegree (embedded (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (returned_gaussian_degree _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalPolynomialWeightedDegreeGaussianEmbedding
