import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalFiniteRoots
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-!
# One actual rectangular Gaussian-rational row-elimination step

A numerical pivot location and its original nonzero field value suffice
for the actual normalization/elimination table. Bounded actual scalar
folds give both homogeneous-system transports. No pivot search, echelon
profile, rank or nonzero annihilator is supplied or claimed here.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowElimination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical qmul_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnegative qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical recode_eq)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell subst_cell)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (table table_length table_row_length table_lookup)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_canonical sum_congr_bounded)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shape (A R N : PTm n) : Fm PTm n := (length A ≐ R) ⋏ .all
  (lt (var 0) (Syn.shift R) ⟶ length (entry (Syn.shift A) (var 0)) ≐ Syn.shift N)
def pivot (A i p : PTm n) : PTm n := recode (cell A i p)
def inverse (A i p : PTm n) : PTm n := reciprocal (pivot A i p)
def normalizedPivot (A i p j : PTm n) : PTm n := qmul (inverse A i p) (cell A i j)
def entryValue (A i p r j : PTm n) : PTm n := sel (eqb r i) (normalizedPivot A i p j)
  (qsub (cell A r j) (qmul (cell A r p) (normalizedPivot A i p j)))
def data (A i p : PTm n) : PTm n := pairT A (pairT i p)
def entryBody : PTm 3 := entryValue (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
def eliminate (A R N i p : PTm n) : PTm n := table entryBody R N (data A i p)
def input (A R N i p : PTm n) : Fm PTm n := shape A R N ⋏
  (lt i R ⋏ (lt p N ⋏ neg (pivot A i p ≐ qzero)))

def dotData (A l r : PTm n) : PTm n := pairT A (pairT l r)
def dotBody : PTm 2 := qmul (cell (fstT (var 1)) (sndT (sndT (var 1))) (var 0))
  (entry (fstT (sndT (var 1))) (var 0))
def rowDot (A N l r : PTm n) : PTm n := sum dotBody N (dotData A l r)
def nullRows (A R N l : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift R) ⟶ rowDot (Syn.shift A) (Syn.shift N) (Syn.shift l) (var 0) ≐ qzero)

@[simp] theorem subst_shape {k : ℕ} (σ : Fin n → PTm k) (A R N : PTm n) :
    (shape A R N).subst σ = shape (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [shape,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_pivot {k : ℕ} (σ : Fin n → PTm k) (A i p : PTm n) :
    Syn.subst σ (pivot A i p) = pivot (Syn.subst σ A) (Syn.subst σ i) (Syn.subst σ p) := by simp [pivot]
@[simp] theorem subst_inverse {k : ℕ} (σ : Fin n → PTm k) (A i p : PTm n) :
    Syn.subst σ (inverse A i p) = inverse (Syn.subst σ A) (Syn.subst σ i) (Syn.subst σ p) := by simp [inverse]
@[simp] theorem subst_normalizedPivot {k : ℕ} (σ : Fin n → PTm k) (A i p j : PTm n) :
    Syn.subst σ (normalizedPivot A i p j) = normalizedPivot (Syn.subst σ A) (Syn.subst σ i)
      (Syn.subst σ p) (Syn.subst σ j) := by simp [normalizedPivot]
@[simp] theorem subst_entryValue {k : ℕ} (σ : Fin n → PTm k) (A i p r j : PTm n) :
    Syn.subst σ (entryValue A i p r j) = entryValue (Syn.subst σ A) (Syn.subst σ i)
      (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ j) := by simp [entryValue,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A i p : PTm n) :
    Syn.subst σ (data A i p) = data (Syn.subst σ A) (Syn.subst σ i) (Syn.subst σ p) := by simp [data]
@[simp] theorem subst_eliminate {k : ℕ} (σ : Fin n → PTm k) (A R N i p : PTm n) :
    Syn.subst σ (eliminate A R N i p) = eliminate (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [eliminate]
@[simp] theorem subst_input {k : ℕ} (σ : Fin n → PTm k) (A R N i p : PTm n) :
    (input A R N i p).subst σ = input (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [input]
@[simp] theorem subst_dotData {k : ℕ} (σ : Fin n → PTm k) (A l r : PTm n) :
    Syn.subst σ (dotData A l r) = dotData (Syn.subst σ A) (Syn.subst σ l) (Syn.subst σ r) := by simp [dotData]
@[simp] theorem subst_rowDot {k : ℕ} (σ : Fin n → PTm k) (A N l r : PTm n) :
    Syn.subst σ (rowDot A N l r) = rowDot (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ l) (Syn.subst σ r) := by simp [rowDot]
@[simp] theorem subst_nullRows {k : ℕ} (σ : Fin n → PTm k) (A R N l : PTm n) :
    (nullRows A R N l).subst σ = nullRows (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ l) := by
  simp [nullRows,Syn.subst_shift,Syn.shift_subst]

theorem entry_body_at (A i p r j : PTm n) : Γ ⊢[PRAAx]
    Syn.subst ![r,j,data A i p] entryBody ≐ entryValue A i p r j := by
  simp only [entryBody,subst_entryValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  simpa only [subst_entryValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (entryValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fstT (data A i p),fstT (sndT (data A i p)),sndT (sndT (data A i p)),r,j])
      (σ' := ![A,i,p,r,j]) (fun k => by
        fin_cases k
        · exact fst_pair _ _
        · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
        · exact .eqRefl _
        · exact .eqRefl _)

theorem output_length (A R N i p : PTm n) : Γ ⊢[PRAAx] length (eliminate A R N i p) ≐ R := table_length _ _ _ _
theorem output_row_length (A R N i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    length (entry (eliminate A R N i p) r) ≐ N := table_row_length _ _ _ _ _ hr
theorem output_shape (A R N i p : PTm n) : Γ ⊢[PRAAx] shape (eliminate A R N i p) R N := by
  refine .andI (output_length _ _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_eliminate] using output_row_length (Syn.shift A) (Syn.shift R)
    (Syn.shift N) (Syn.shift i) (Syn.shift p) (var 0) Prf.hyp0
theorem output_lookup (A R N i p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    cell (eliminate A R N i p) r j ≐ entryValue A i p r j :=
  (table_lookup _ _ _ _ _ _ hr hj).eqTrans (entry_body_at _ _ _ _ _)

theorem same_row (A i p j : PTm n) : Γ ⊢[PRAAx] entryValue A i p i j ≐ normalizedPivot A i p j := sel_one (eqb_of_eq (.eqRefl _))
theorem other_row (A i p r j : PTm n) (h : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    entryValue A i p r j ≐ qsub (cell A r j) (qmul (cell A r p) (normalizedPivot A i p j)) := sel_zero (eqb_of_ne h)
theorem entry_canonical (A i p r j : PTm n) : Γ ⊢[PRAAx] canonical (entryValue A i p r j) := by
  refine .orE (eq_or_ne r i) ?_ ?_
  · have e : (r ≐ i) :: Γ ⊢[PRAAx] entryValue A i p r j ≐ normalizedPivot A i p j :=
      sel_one (eqb_of_eq Prf.hyp0)
    exact GaussianRationalHorner.canonical_congr e (qmul_canonical _ _)
  · exact GaussianRationalHorner.canonical_congr (other_row A i p r j Prf.hyp0) (qsub_canonical _ _)
theorem output_canonical (A R N i p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    canonical (cell (eliminate A R N i p) r j) :=
  GaussianRationalHorner.canonical_congr (output_lookup _ _ _ _ _ _ _ hr hj) (entry_canonical _ _ _ _ _)

theorem pivot_inverse (A i p : PTm n) (h : Γ ⊢[PRAAx] neg (pivot A i p ≐ qzero)) : Γ ⊢[PRAAx]
    qmul (pivot A i p) (inverse A i p) ≐ qone :=
  reciprocal_identity _ (GaussianRationalFiniteRoots.norm_positive_of_nonzero _ (recode_canonical _) h)
theorem pivot_column (A i p : PTm n) (h : Γ ⊢[PRAAx] neg (pivot A i p ≐ qzero)) : Γ ⊢[PRAAx]
    normalizedPivot A i p p ≐ qone :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm.eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (pivot_inverse A i p h))

theorem dot_body_at (A l r j : PTm n) : Γ ⊢[PRAAx]
    inst2 dotBody j (dotData A l r) ≐ qmul (cell A r j) (entry l j) := by
  simp only [dotBody,inst2,GaussianRationalHorner.subst_qmul,subst_cell,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (entry_congr (entry_congr (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))) (.eqRefl _))
    (entry_congr ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))
theorem row_dot_canonical (A N l r : PTm n) : Γ ⊢[PRAAx] canonical (rowDot A N l r) := sum_canonical _ _ _

theorem normalized_lookup (A R N i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    cell (eliminate A R N i p) i j ≐ normalizedPivot A i p j :=
  (output_lookup _ _ _ _ _ _ _ hi hj).eqTrans (same_row _ _ _ _)
theorem eliminated_lookup (A R N i p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hj : Γ ⊢[PRAAx] lt j N)
    (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    cell (eliminate A R N i p) r j ≐ qsub (cell A r j) (qmul (cell A r p) (normalizedPivot A i p j)) :=
  (output_lookup _ _ _ _ _ _ _ hr hj).eqTrans (other_row _ _ _ _ _ hne)
theorem output_pivot_one (A R N i p : PTm n) (h : Γ ⊢[PRAAx] input A R N i p) : Γ ⊢[PRAAx]
    cell (eliminate A R N i p) i p ≐ qone :=
  (normalized_lookup _ _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))).eqTrans
    (pivot_column _ _ _ (.andE₂ (.andE₂ (.andE₂ h))))
theorem output_pivot_zero (A R N i p r : PTm n) (h : Γ ⊢[PRAAx] input A R N i p)
    (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    cell (eliminate A R N i p) r p ≐ qzero := by
  have product : Γ ⊢[PRAAx] qmul (cell A r p) (normalizedPivot A i p p) ≐ recode (cell A r p) :=
    (qmul_congr (.eqRefl _) (pivot_column _ _ _ (.andE₂ (.andE₂ (.andE₂ h))))).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalFiniteProduct.raw_one_left _))
  have sub : Γ ⊢[PRAAx] qsub (cell A r p) (recode (cell A r p)) ≐ qzero :=
    (GaussianRationalValueEquality.recode_eq_iff_difference_zero _ _).iffMp
      (recode_eq _ (recode_canonical _)).eqSymm
  exact (eliminated_lookup _ _ _ _ _ _ _ hr (.andE₁ (.andE₂ (.andE₂ h))) hne).eqTrans
    ((qsub_congr (.eqRefl _) product).eqTrans sub)

theorem row_dot_congr {A A' N N' l l' r r' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hl : Γ ⊢[PRAAx] l ≐ l') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    rowDot A N l r ≐ rowDot A' N' l' r' :=
  GaussianRationalFiniteSum.sum_index_congr dotBody hN (congrPairT hA (congrPairT hl hr))

theorem dot_normalized (A R N i p l : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    rowDot (eliminate A R N i p) N l i ≐ qmul (inverse A i p) (rowDot A N l i) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift R) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hi.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual dotBody
      (GaussianRationalFiniteSum.multiplyBody dotBody) N (dotData (eliminate A R N i p) l i)
        (pairT (inverse A i p) (dotData A l i)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have low := (dot_body_at (Γ := Δ) (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
      (Syn.shift l) (Syn.shift i) (var 0)).eqTrans
      ((qmul_congr (normalized_lookup _ _ _ _ _ _ hs.wk Prf.hyp0) (.eqRefl _)).eqTrans
        (GaussianReciprocalHorner.qmul_associative _ _ _))
    have high := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) dotBody (inverse (Syn.shift A) (Syn.shift i) (Syn.shift p))
      (var 0) (dotData (Syn.shift A) (Syn.shift l) (Syn.shift i))).eqTrans
      (qmul_congr (.eqRefl _) (dot_body_at _ _ _ _))
    simpa only [Δ,Syn.shift,subst_dotData,subst_eliminate,subst_pairT,subst_inverse] using low.eqTrans high.eqSymm
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalFiniteSum.sum_multiply _ _ _ _)

theorem dot_pivot_recovery (A R N i p l : PTm n) (h : Γ ⊢[PRAAx] input A R N i p) : Γ ⊢[PRAAx]
    qmul (pivot A i p) (rowDot (eliminate A R N i p) N l i) ≐ rowDot A N l i :=
  (qmul_congr (.eqRefl _) (dot_normalized _ _ _ _ _ _ (.andE₁ (.andE₂ h)))).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (pivot_inverse _ _ _ (.andE₂ (.andE₂ (.andE₂ h)))) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (row_dot_canonical _ _ _ _)))))

theorem distribute_right (a b c : PTm n) : Γ ⊢[PRAAx]
    qmul (qadd a b) c ≐ qadd (qmul a c) (qmul b c) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

theorem dot_eliminated (A R N i p l r : PTm n)
    (hi : Γ ⊢[PRAAx] lt i R) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    rowDot (eliminate A R N i p) N l r ≐ qadd (rowDot A N l r)
      (qmul (qnegative (cell A r p)) (rowDot (eliminate A R N i p) N l i)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift R) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hi.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift R) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] neg (Syn.shift r ≐ Syn.shift i) := by simpa only [Fm.shift,subst_neg,Fm.subst_eq,Syn.shift] using hne.shift
  apply GaussianInverseBinomialRows.linear_sum dotBody dotBody dotBody N
    (dotData (eliminate A R N i p) l r) (dotData A l r) (dotData (eliminate A R N i p) l i) (qnegative (cell A r p))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have low := (dot_body_at (Γ := Δ) (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
    (Syn.shift l) (Syn.shift r) (var 0)).eqTrans
    ((qmul_congr ((eliminated_lookup _ _ _ _ _ _ _ rs.wk Prf.hyp0 ns.wk).eqTrans
      (GaussianInverseBinomialRows.difference_negative_product _ _ _)) (.eqRefl _)).eqTrans
      ((distribute_right _ _ _).eqTrans
        (qadd_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_associative _ _ _))))
  have high := qadd_congr (dot_body_at (Γ := Δ) (Syn.shift A) (Syn.shift l) (Syn.shift r) (var 0))
    (qmul_congr (.eqRefl (qnegative (cell (Syn.shift A) (Syn.shift r) (Syn.shift p))))
      ((dot_body_at (Γ := Δ) (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
        (Syn.shift l) (Syn.shift i) (var 0)).eqTrans
        (qmul_congr (normalized_lookup _ _ _ _ _ _ hs.wk Prf.hyp0) (.eqRefl _))))
  simpa only [Δ,Syn.shift,subst_dotData,subst_eliminate,GaussianRationalMetric.subst_qnegative,
    subst_cell] using low.eqTrans high.eqSymm

theorem null_at (A R N l r : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N l) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    rowDot A N l r ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt r R ⟶ rowDot A N l r ≐ qzero := by
    simpa only [nullRows,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_rowDot,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,GaussianRationalHorner.subst_qzero] using h.allE r
  exact .impE rule hr

theorem off_dot_when_pivot_zero (A R N i p l r : PTm n)
    (hi : Γ ⊢[PRAAx] lt i R) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i))
    (hz : Γ ⊢[PRAAx] rowDot (eliminate A R N i p) N l i ≐ qzero) : Γ ⊢[PRAAx]
    rowDot (eliminate A R N i p) N l r ≐ rowDot A N l r :=
  (dot_eliminated _ _ _ _ _ _ _ hi hr hne).eqTrans
    ((qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _) hz).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (row_dot_canonical _ _ _ _)))

theorem null_forward (A R N i p l : PTm n) (hInput : Γ ⊢[PRAAx] input A R N i p)
    (hNull : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx] nullRows (eliminate A R N i p) R N l := by
  have pivotZero : Γ ⊢[PRAAx] rowDot (eliminate A R N i p) N l i ≐ qzero :=
    (dot_normalized _ _ _ _ _ _ (.andE₁ (.andE₂ hInput))).eqTrans
      ((qmul_congr (.eqRefl _) (null_at _ _ _ _ _ hNull (.andE₁ (.andE₂ hInput)))).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))
  have ps : Γ.map Fm.shift ⊢[PRAAx]
      rowDot (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
        (Syn.shift N) (Syn.shift l) (Syn.shift i) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_rowDot,subst_eliminate,Syn.shift,GaussianRationalHorner.subst_qzero] using pivotZero.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using hInput.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l) := by
    simpa only [Fm.shift,subst_nullRows,Syn.shift] using hNull.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have result : Δ ⊢[PRAAx] rowDot (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
      (Syn.shift N) (Syn.shift l) (var 0) ≐ qzero := by
    refine .orE (eq_or_ne (var 0) (Syn.shift i)) ?_ ?_
    · exact (row_dot_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans ps.wk.wk
    · exact (off_dot_when_pivot_zero _ _ _ _ _ _ _ (.andE₁ (.andE₂ hs.wk.wk)) Prf.hyp1 Prf.hyp0 ps.wk.wk).eqTrans
        (null_at _ _ _ _ _ ns.wk.wk Prf.hyp1)
  simpa only [Δ,Syn.shift,subst_eliminate] using result

theorem null_backward (A R N i p l : PTm n) (hInput : Γ ⊢[PRAAx] input A R N i p)
    (hNull : Γ ⊢[PRAAx] nullRows (eliminate A R N i p) R N l) : Γ ⊢[PRAAx] nullRows A R N l := by
  have pivotNew := null_at (eliminate A R N i p) R N l i hNull (.andE₁ (.andE₂ hInput))
  have pivotOld : Γ ⊢[PRAAx] rowDot A N l i ≐ qzero :=
    (dot_pivot_recovery _ _ _ _ _ _ hInput).eqSymm.eqTrans
      ((qmul_congr (.eqRefl _) pivotNew).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))
  have ps : Γ.map Fm.shift ⊢[PRAAx] rowDot (Syn.shift A) (Syn.shift N) (Syn.shift l) (Syn.shift i) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_rowDot,Syn.shift,GaussianRationalHorner.subst_qzero] using pivotOld.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] rowDot
      (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p))
        (Syn.shift N) (Syn.shift l) (Syn.shift i) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_rowDot,subst_eliminate,Syn.shift,GaussianRationalHorner.subst_qzero] using pivotNew.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using hInput.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] nullRows
      (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p)) (Syn.shift R) (Syn.shift N) (Syn.shift l) := by
    simpa only [Fm.shift,subst_nullRows,subst_eliminate,Syn.shift] using hNull.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  refine .orE (eq_or_ne (var 0) (Syn.shift i)) ?_ ?_
  · exact (row_dot_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans ps.wk.wk
  · exact (off_dot_when_pivot_zero _ _ _ _ _ _ _ (.andE₁ (.andE₂ hs.wk.wk)) Prf.hyp1 Prf.hyp0 zs.wk.wk).eqSymm.eqTrans
      (null_at _ _ _ _ _ ns.wk.wk Prf.hyp1)

theorem null_equivalence (A R N i p l : PTm n) (hInput : Γ ⊢[PRAAx] input A R N i p) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (eliminate A R N i p) R N l) :=
  .andI (.impI (null_forward _ _ _ _ _ _ hInput.wk Prf.hyp0))
    (.impI (null_backward _ _ _ _ _ _ hInput.wk Prf.hyp0))

theorem empty_dot (A l r : PTm n) : Γ ⊢[PRAAx] rowDot A zero l r ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _

theorem null_rows_congr {A B R N l : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (h : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx] nullRows B R N l := by
  simpa only [subst_nullRows,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (nullRows (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
      ![A,R,N,l] ![B,R,N,l] (fun i => by fin_cases i; exact hA; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [subst_nullRows,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using h)

/-! This PR5 returns the actual rectangular table itself. Lambda is an
independent numerical proof query; no presumed null vector is a producer input. -/
def outputF : PR 5 := PTm.toPR (eliminate (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R N i p : PTm n) : PTm n := app outputF ![A,R,N,i,p]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N i p : PTm n) :
    Syn.subst σ (run A R N i p) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ i) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (A R N i p : PTm n) : Γ ⊢[PRAAx] run A R N i p ≐ eliminate A R N i p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (eliminate (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,N,i,p]
theorem returned_lookup (A R N i p r j : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    cell (run A R N i p) r j ≐ entryValue A i p r j :=
  (entry_congr (entry_congr (program_at _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (output_lookup _ _ _ _ _ _ _ hr hj)
theorem returned_pivot_one (A R N i p : PTm n) (h : Γ ⊢[PRAAx] input A R N i p) : Γ ⊢[PRAAx]
    cell (run A R N i p) i p ≐ qone :=
  (entry_congr (entry_congr (program_at _ _ _ _ _) (.eqRefl _)) (.eqRefl _)).eqTrans (output_pivot_one _ _ _ _ _ h)
theorem returned_null_equivalence (A R N i p l : PTm n) (hInput : Γ ⊢[PRAAx] input A R N i p) : Γ ⊢[PRAAx]
    Fm.iff (nullRows A R N l) (nullRows (run A R N i p) R N l) :=
  .andI (.impI (null_rows_congr (program_at _ _ _ _ _).wk.eqSymm
    (null_forward _ _ _ _ _ _ hInput.wk Prf.hyp0)))
    (.impI (null_backward _ _ _ _ _ _ hInput.wk
      (null_rows_congr (program_at _ _ _ _ _).wk Prf.hyp0)))

/-! All rectangular dimensions, original codes, pivot locations and
independent vector queries remain numerical in these ordinary sequents.
No rank, echelon or nonzero-kernel construction is claimed. -/
theorem actual_rectangular_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2)) :=
  closeUniv 5 (output_shape _ _ _ _ _)
theorem actual_output_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 5) (var 1) ⟶ lt (var 6) (var 2) ⟶
      canonical (cell (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (output_canonical _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_pivot_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      cell (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) (var 4) ≐ qone) :=
  closeUniv 5 (.impI (output_pivot_one _ _ _ _ _ Prf.hyp0))
theorem actual_pivot_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 1) ⟶ neg (var 5 ≐ var 3) ⟶
      cell (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 4) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (.impI (output_pivot_zero _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_normalized_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 3) (var 1) ⟶ rowDot (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5) (var 3) ≐
      qmul (inverse (var 0) (var 3) (var 4)) (rowDot (var 0) (var 2) (var 5) (var 3))) :=
  closeUniv 6 (.impI (dot_normalized _ _ _ _ _ _ Prf.hyp0))
theorem actual_eliminated_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 3) (var 1) ⟶ lt (var 6) (var 1) ⟶ neg (var 6 ≐ var 3) ⟶
      rowDot (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5) (var 6) ≐
        qadd (rowDot (var 0) (var 2) (var 5) (var 6))
          (qmul (qnegative (cell (var 0) (var 6) (var 4)))
            (rowDot (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 5) (var 3)))) :=
  closeUniv 7 (.impI (.impI (.impI (dot_eliminated _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (nullRows (var 0) (var 1) (var 2) (var 5))
        (nullRows (eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (null_equivalence _ _ _ _ _ _ Prf.hyp0))
theorem actual_empty_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowDot (var 0) zero (var 1) (var 2) ≐ qzero) := closeUniv 3 (empty_dot _ _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ eliminate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_null_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (nullRows (var 0) (var 1) (var 2) (var 5))
        (nullRows (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (returned_null_equivalence _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalRowElimination
