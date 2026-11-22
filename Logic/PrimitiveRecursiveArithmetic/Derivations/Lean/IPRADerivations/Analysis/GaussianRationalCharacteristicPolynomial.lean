import IPRADerivations.Analysis.GaussianScalarIdentityDeterminant
import IPRADerivations.Analysis.GaussianRationalPolynomialProductDegree

/-!
# The actual characteristic polynomial at numerical matrix size

The original scalar table is read by a fixed two-coefficient cell program.
The SAME existing polynomial determinant constructs det(X I - A). Its
leading coefficient is derived by transporting the actual leading-slot
fold to the numerical scalar determinant of the leading-cell table.
No determinant, monicity or output-coefficient law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCharacteristicPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul evaluate canonical canonical_congr qmul_canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qmul_congr qadd_congr canonicalCoefficients)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq zeroPrefix)
open GaussianPolynomialDeterminantTerms (cell factor stage stage_zero stage_succ stage_length stage_canonical)
open GaussianRationalFiberVandermonde (table table_lookup table_length table_row_length delta)
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_canonical)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def headBody : PTm 3 := recode (entry (cell (var 2) (var 0) (var 1)) zero)
def headTable (M m : PTm n) : PTm n := table headBody m m M
def headProduct (M m w j : PTm n) : PTm n := qprod GaussianScalarDeterminant.factorBody j
  (GaussianScalarDeterminant.factorData (headTable M m) m w)
@[simp] theorem subst_headTable {l : ℕ} (σ : Fin n → PTm l) (M m : PTm n) :
    Syn.subst σ (headTable M m) = headTable (Syn.subst σ M) (Syn.subst σ m) := by simp [headTable]
@[simp] theorem subst_headProduct {l : ℕ} (σ : Fin n → PTm l) (M m w j : PTm n) :
    Syn.subst σ (headProduct M m w j) = headProduct (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ j) := by simp [headProduct]

theorem head_table_lookup (M m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (headTable M m) r j ≐ recode (entry (cell M r j) zero) := by
  simpa [headTable,headBody] using table_lookup headBody m m M r j hr hj
theorem zero_prefix_zero (C : PTm n) : Γ ⊢[PRAAx] zeroPrefix C zero := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (Syn.shift zero) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) zero := by simpa [Syn.shift] using (Prf.hyp0 : lt (var 0) (Syn.shift zero) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift zero))
  exact lt_zero_absurd _ hi
theorem coefficient_index {P Q M t k k' : PTm n} (h : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    GaussianRationalPolynomialProduct.coefficient P Q M t k ≐ GaussianRationalPolynomialProduct.coefficient P Q M t k' :=
  GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) h)))
theorem product_head (P Q N M : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianRationalPolynomialProduct.product P Q N M) zero ≐ qmul (recode (entry P zero)) (recode (entry Q zero)) :=
  (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ (zero_le _)).eqTrans
    ((coefficient_index (add_zero zero).eqSymm).eqTrans
      (GaussianRationalPolynomialProductDegree.leading_coefficient _ _ _ _ zero zero (zero_prefix_zero _) (zero_prefix_zero _)
        (zero_le _) (zero_le _)))

theorem head_product_zero (M m w : PTm n) : Γ ⊢[PRAAx] headProduct M m w zero ≐ qone := product_zero _ _
theorem head_product_succ (M m w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    headProduct M m w (succ j) ≐ qmul (headProduct M m w j) (recode (entry (factor M m w j) zero)) :=
  (product_succ _ _ _).eqTrans (qmul_congr (.eqRefl _)
    ((GaussianScalarDeterminant.factor_body_at _ _ _ _).eqTrans
      (head_table_lookup _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ hj) hj)))

def headLaw (M m L w j : PTm n) : Fm PTm n := le j m ⟶ entry (stage M m L w j) zero ≐ headProduct M m w j
@[simp] theorem subst_headLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (headLaw M m L w j).subst σ = headLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by
  simp [headLaw]
theorem stage_head (M m L w j : PTm n) (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    entry (stage M m L w j) zero ≐ headProduct M m w j := by
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((entry_congr (stage_zero M m L w) (.eqRefl _)).eqTrans
        ((GaussianRationalMonicReduction.singleton_lookup qone).eqTrans (head_product_zero M m w).eqSymm))
    · simp only [subst_headLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift m) :: headLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] entry (stage (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)) zero ≐
          headProduct (Syn.shift M) (Syn.shift m) (Syn.shift w) (var 0) := .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have recoded := (recode_congr ih).eqTrans (recode_eq _ (product_canonical _ _ _))
      exact (entry_congr (stage_succ (Γ := Δ) (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)) (.eqRefl _)).eqTrans
        ((product_head _ _ _ _).eqTrans ((qmul_congr recoded (.eqRefl _)).eqTrans
          (head_product_succ _ _ _ _ Prf.hyp0).eqSymm))
  have atJ : Γ ⊢[PRAAx] headLaw M m L w j := by
    simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE atJ hj

theorem determinant_head (M m L : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianPolynomialDeterminant.determinant M m L) zero ≐ GaussianScalarDeterminant.scalarDet (headTable M m) m := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianPolynomialDeterminant.coefficientBody
      GaussianScalarDeterminant.signedBody (Foundations.RuntimePermutationWords.count m)
      (GaussianPolynomialDeterminantTerms.data M m L zero) (pairT (headTable M m) m) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift
    have e := (GaussianPolynomialDeterminant.coefficient_body_at (Γ := Δ) (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) zero).eqTrans
      ((qmul_congr (.eqRefl _) (stage_head (Syn.shift M) (Syn.shift m) (Syn.shift L)
        (GaussianPolynomialDeterminant.wordCode (Syn.shift m) (var 0)) (Syn.shift m) (le_refl _))).eqTrans
          (GaussianScalarDeterminant.signed_body_at (headTable (Syn.shift M) (Syn.shift m)) (Syn.shift m) (var 0)).eqSymm)
    simpa only [Δ,Syn.shift,Foundations.RuntimePermutationWords.subst_count,GaussianPolynomialDeterminantTerms.subst_data,
      subst_pairT,subst_headTable,ConciseIPRA.PTm.subst_zero] using e
  exact (GaussianPolynomialDeterminant.coefficient_leibniz _ _ _ _ (zero_le _)).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianScalarDeterminant.scalar_leibniz _ _).eqSymm)

/-! Two actual descending coefficients, with no scalar zero-row shortcut. -/
def cellData (A r j : PTm n) : PTm n := pairT A (pairT r j)
def cellCoefficient (A r j k : PTm n) : PTm n := sel (eqb k zero) (delta r j) (qnegative (cell A r j))
def cellBody : PTm 2 := cellCoefficient (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def cellPolynomial (A r j : PTm n) : PTm n := sequence cellBody two (cellData A r j)
def characteristicBody : PTm 3 := cellPolynomial (var 2) (var 0) (var 1)
def characteristicTable (A m : PTm n) : PTm n := table characteristicBody m m A
def polynomial (A m : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant (characteristicTable A m) m one
@[simp] theorem subst_cellData {l : ℕ} (σ : Fin n → PTm l) (A r j : PTm n) :
    Syn.subst σ (cellData A r j) = cellData (Syn.subst σ A) (Syn.subst σ r) (Syn.subst σ j) := by simp [cellData]
@[simp] theorem subst_cellCoefficient {l : ℕ} (σ : Fin n → PTm l) (A r j k : PTm n) :
    Syn.subst σ (cellCoefficient A r j k) = cellCoefficient (Syn.subst σ A) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ k) := by simp [cellCoefficient,sel]
@[simp] theorem subst_cellPolynomial {l : ℕ} (σ : Fin n → PTm l) (A r j : PTm n) :
    Syn.subst σ (cellPolynomial A r j) = cellPolynomial (Syn.subst σ A) (Syn.subst σ r) (Syn.subst σ j) := by simp [cellPolynomial]
@[simp] theorem subst_characteristicTable {l : ℕ} (σ : Fin n → PTm l) (A m : PTm n) :
    Syn.subst σ (characteristicTable A m) = characteristicTable (Syn.subst σ A) (Syn.subst σ m) := by simp [characteristicTable]
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (A m : PTm n) :
    Syn.subst σ (polynomial A m) = polynomial (Syn.subst σ A) (Syn.subst σ m) := by simp [polynomial]

theorem cell_coefficient_congr {A B r s j k i t : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B) (hr : Γ ⊢[PRAAx] r ≐ s)
    (hj : Γ ⊢[PRAAx] j ≐ k) (hi : Γ ⊢[PRAAx] i ≐ t) : Γ ⊢[PRAAx] cellCoefficient A r j i ≐ cellCoefficient B s k t := by
  simpa only [subst_cellCoefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ)
      (cellCoefficient (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![A,r,j,i]) (σ' := ![B,s,k,t])
      (fun q => by fin_cases q; exact hA; exact hr; exact hj; exact hi)
theorem cell_body_at (A r j k : PTm n) : Γ ⊢[PRAAx] inst2 cellBody k (cellData A r j) ≐ cellCoefficient A r j k := by
  simp only [cellBody,inst2,subst_cellCoefficient,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact cell_coefficient_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem cell_length (A r j : PTm n) : Γ ⊢[PRAAx] length (cellPolynomial A r j) ≐ two := sequence_length _ _ _
theorem cell_lookup (A r j k : PTm n) (hk : Γ ⊢[PRAAx] lt k two) : Γ ⊢[PRAAx]
    entry (cellPolynomial A r j) k ≐ cellCoefficient A r j k := (sequence_decode cellBody hk).eqTrans (cell_body_at _ _ _ _)
theorem cell_head (A r j : PTm n) : Γ ⊢[PRAAx] entry (cellPolynomial A r j) zero ≐ delta r j :=
  (cell_lookup _ _ _ _ (zero_lt_succ one)).eqTrans (sel_one (eqb_of_eq (.eqRefl zero)))
theorem cell_tail (A r j : PTm n) : Γ ⊢[PRAAx] entry (cellPolynomial A r j) one ≐ qnegative (cell A r j) :=
  (cell_lookup _ _ _ _ (le_refl two)).eqTrans (sel_zero (eqb_of_ne (.impI (succ_ne_zero Prf.hyp0))))
theorem cell_coefficient_canonical (A r j k : PTm n) : Γ ⊢[PRAAx] canonical (cellCoefficient A r j k) := by
  refine .orE (eq_or_ne k zero) ?_ ?_
  · exact canonical_congr (sel_one (eqb_of_eq Prf.hyp0)) (GaussianRationalFiberVandermonde.delta_canonical _ _)
  · exact canonical_congr (sel_zero (eqb_of_ne Prf.hyp0)) (qnegative_canonical _)
theorem cell_canonical (A r j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (cellPolynomial A r j) := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (length (Syn.shift (cellPolynomial A r j))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) two :=
    lt_congr (.eqRefl _) (by simpa [Syn.shift] using cell_length (Syn.shift A) (Syn.shift r) (Syn.shift j)) Prf.hyp0
  simpa only [Syn.shift,subst_cellPolynomial] using canonical_congr (cell_lookup (Syn.shift A) (Syn.shift r) (Syn.shift j) (var 0) hi)
    (cell_coefficient_canonical _ _ _ _)
theorem table_lookup_at (A m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (characteristicTable A m) r j ≐ cellPolynomial A r j := by
  simpa [characteristicTable,characteristicBody] using table_lookup characteristicBody m m A r j hr hj
theorem table_shape (A m : PTm n) : Γ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.tableShape (characteristicTable A m) m one := by
  refine .andI (table_length _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI (.allI (.impI ?_)))))
  · simpa only [Syn.shift,subst_characteristicTable,characteristicTable,GaussianRationalFiberVandermonde.subst_table] using table_row_length
      (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) characteristicBody (Syn.shift m) (Syn.shift m) (Syn.shift A) (var 0) Prf.hyp0
  · let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
    have e := (congrFst (table_lookup_at (Γ := Δ) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (var 1) (var 0) hr Prf.hyp0)).eqTrans (cell_length _ _ _)
    simpa [Δ,GaussianPolynomialDeterminantTerms.rowCells,Syn.shift,length,one,two] using e

theorem head_identity (A m : PTm n) : Γ ⊢[PRAAx] GaussianScalarIdentityDeterminant.identityEntries (headTable (characteristicTable A m) m) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have e := (head_table_lookup (Γ := Δ) (characteristicTable (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)))
      (Syn.shift (Syn.shift m)) (var 1) (var 0) hr Prf.hyp0).eqTrans
    ((recode_congr ((entry_congr (table_lookup_at _ _ _ _ hr Prf.hyp0) (.eqRefl _)).eqTrans (cell_head _ _ _))).eqTrans
      (recode_eq _ (GaussianRationalFiberVandermonde.delta_canonical _ _)))
  simpa only [Δ,GaussianScalarIdentityDeterminant.identityEntries,GaussianScalarIdentityDeterminant.identityRow,
    Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_headTable,subst_characteristicTable] using e
theorem polynomial_length (A m : PTm n) : Γ ⊢[PRAAx] length (polynomial A m) ≐ succ m :=
  (GaussianPolynomialDeterminant.determinant_length _ _ _).eqTrans (congrSucc (by ipra_ring))
theorem polynomial_canonical (A m : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial A m) := GaussianPolynomialDeterminant.determinant_canonical _ _ _
theorem polynomial_monic (A m : PTm n) : Γ ⊢[PRAAx] entry (polynomial A m) zero ≐ qone :=
  (determinant_head _ _ _).eqTrans (GaussianScalarIdentityDeterminant.identity_det_of_entries _ _ (head_identity A m))

def shiftedWeight (A z r j : PTm n) : PTm n := GaussianRationalMetric.qsub (qmul z (delta r j)) (cell A r j)
def shiftedBody : PTm 3 := shiftedWeight (fstT (var 2)) (sndT (var 2)) (var 0) (var 1)
def shiftedTable (A m z : PTm n) : PTm n := table shiftedBody m m (pairT A z)
@[simp] theorem subst_shiftedWeight {l : ℕ} (σ : Fin n → PTm l) (A z r j : PTm n) :
    Syn.subst σ (shiftedWeight A z r j) = shiftedWeight (Syn.subst σ A) (Syn.subst σ z) (Syn.subst σ r) (Syn.subst σ j) := by simp [shiftedWeight]
@[simp] theorem subst_shiftedTable {l : ℕ} (σ : Fin n → PTm l) (A m z : PTm n) :
    Syn.subst σ (shiftedTable A m z) = shiftedTable (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ z) := by simp [shiftedTable]
theorem shifted_weight_congr {A B z y r s j k : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B) (hz : Γ ⊢[PRAAx] z ≐ y)
    (hr : Γ ⊢[PRAAx] r ≐ s) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] shiftedWeight A z r j ≐ shiftedWeight B y s k := by
  simpa only [subst_shiftedWeight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ)
      (shiftedWeight (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![A,z,r,j]) (σ' := ![B,y,s,k])
      (fun q => by fin_cases q; exact hA; exact hz; exact hr; exact hj)
theorem shifted_lookup (A m z r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (shiftedTable A m z) r j ≐ shiftedWeight A z r j := by
  have e := table_lookup shiftedBody m m (pairT A z) r j hr hj
  simp only [shiftedBody,subst_shiftedWeight,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  exact e.eqTrans (shifted_weight_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _) (.eqRefl _))
theorem cell_evaluation (A r j z : PTm n) : Γ ⊢[PRAAx] evaluate (cellPolynomial A r j) z ≐ shiftedWeight A z r j := by
  have first : Γ ⊢[PRAAx] GaussianRationalHorner.horner (cellPolynomial A r j) z one ≐ delta r j :=
    (GaussianRationalSyntheticDivision.first_prefix _ _).eqTrans
      ((qadd_congr (.eqRefl _) (cell_head _ _ _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalFiberVandermonde.delta_canonical _ _)))
  exact (congrAp3 GaussianRationalHorner.hornerF (cell_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ one).eqTrans
      ((qadd_congr (qmul_congr first (.eqRefl _)) (cell_tail _ _ _)).eqTrans
        (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _))))
theorem evaluated_cells (A m z : PTm n) : Γ ⊢[PRAAx] GaussianScalarDeterminant.scalarCellsEqual
    (GaussianScalarDeterminant.evaluatedTable (characteristicTable A m) m z) (shiftedTable A m z) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have e := (GaussianScalarDeterminant.evaluated_lookup (Γ := Δ)
      (characteristicTable (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m))) (Syn.shift (Syn.shift m))
      (Syn.shift (Syn.shift z)) (var 1) (var 0) hr Prf.hyp0).eqTrans
    ((GaussianRationalMonicReduction.evaluate_congr (table_lookup_at _ _ _ _ hr Prf.hyp0) (.eqRefl _)).eqTrans
      ((cell_evaluation _ _ _ _).eqTrans (shifted_lookup _ _ _ _ _ hr Prf.hyp0).eqSymm))
  simpa only [Δ,GaussianScalarDeterminant.scalarCellsEqual,GaussianScalarDeterminant.scalarRowEqual,
    Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,GaussianScalarDeterminant.subst_evaluatedTable,
    subst_characteristicTable,subst_shiftedTable] using GaussianRationalValueEquality.value_equal_of_code e
theorem polynomial_evaluation (A m z : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial A m) z ≐ GaussianScalarDeterminant.scalarDet (shiftedTable A m z) m :=
  (GaussianScalarDeterminant.determinant_evaluation_specialization _ _ _ _ (table_shape A m)).eqTrans
    (GaussianScalarDeterminant.scalar_det_congr _ _ _ (evaluated_cells A m z))

def coefficient (A m i : PTm n) : PTm n := entry (polynomial A m) i
def polynomialF : PR 2 := PTm.toPR (polynomial (var 0) (var 1))
def coefficientF : PR 3 := PTm.toPR (coefficient (var 0) (var 1) (var 2))
def run (A m : PTm n) : PTm n := ap2 polynomialF A m
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (A m i : PTm n) :
    Syn.subst σ (coefficient A m i) = coefficient (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ i) := by simp [coefficient]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (A m : PTm n) :
    Syn.subst σ (run A m) = run (Syn.subst σ A) (Syn.subst σ m) := by simp [run]
theorem program_at (A m : PTm n) : Γ ⊢[PRAAx] run A m ≐ polynomial A m := by
  simpa [run,polynomialF,ap2] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) : PTm 2) ![A,m]
theorem coefficient_at (A m i : PTm n) : Γ ⊢[PRAAx] ap3 coefficientF A m i ≐ coefficient A m i := by
  simpa [coefficientF,ap3] using toPR_eq (Γ := Γ) (coefficient (var 0) (var 1) (var 2) : PTm 3) ![A,m,i]
theorem coefficient_canonical (A m i : PTm n) (hi : Γ ⊢[PRAAx] le i m) : Γ ⊢[PRAAx] canonical (coefficient A m i) :=
  GaussianRationalSyntheticDivision.canonical_coefficient_at _ _ (polynomial_canonical A m)
    (lt_congr (.eqRefl _) (polynomial_length A m).eqSymm ((succ_monus_succ _ _).eqTrans hi))
theorem returned_length (A m : PTm n) : Γ ⊢[PRAAx] length (run A m) ≐ succ m :=
  (congrFst (program_at A m)).eqTrans (polynomial_length A m)
theorem returned_monic (A m : PTm n) : Γ ⊢[PRAAx] entry (run A m) zero ≐ qone :=
  (entry_congr (program_at A m) (.eqRefl _)).eqTrans (polynomial_monic A m)
theorem returned_canonical (A m : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run A m) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (program_at A m) (polynomial_canonical A m)
theorem returned_evaluation (A m z : PTm n) : Γ ⊢[PRAAx]
    evaluate (run A m) z ≐ GaussianScalarDeterminant.scalarDet (shiftedTable A m z) m :=
  (GaussianRationalMonicReduction.evaluate_congr (program_at A m) (.eqRefl _)).eqTrans (polynomial_evaluation A m z)

theorem actual_determinant_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (GaussianPolynomialDeterminant.determinant (var 0) (var 1) (var 2)) zero ≐
      GaussianScalarDeterminant.scalarDet (headTable (var 0) (var 1)) (var 1)) := closeUniv 3 (determinant_head _ _ _)
theorem actual_characteristic_table_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianPolynomialDeterminantTerms.tableShape (characteristicTable (var 0) (var 1)) (var 1) one) := closeUniv 2 (table_shape _ _)
theorem actual_characteristic_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (polynomial (var 0) (var 1)) ≐ succ (var 1)) := closeUniv 2 (polynomial_length _ _)
theorem actual_characteristic_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (polynomial (var 0) (var 1)) zero ≐ qone) := closeUniv 2 (polynomial_monic _ _)
theorem actual_characteristic_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (polynomial (var 0) (var 1)) (var 2) ≐ GaussianScalarDeterminant.scalarDet (shiftedTable (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (polynomial_evaluation _ _ _)
theorem actual_characteristic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ polynomial (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_characteristic_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 coefficientF (var 0) (var 1) (var 2) ≐ coefficient (var 0) (var 1) (var 2)) := closeUniv 3 (coefficient_at _ _ _)
theorem actual_characteristic_coefficient_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ canonical (coefficient (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (coefficient_canonical _ _ _ Prf.hyp0))
theorem actual_returned_characteristic_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (run (var 0) (var 1)) ≐ succ (var 1)) := closeUniv 2 (returned_length _ _)
theorem actual_returned_characteristic_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (run (var 0) (var 1)) zero ≐ qone) := closeUniv 2 (returned_monic _ _)
theorem actual_returned_characteristic_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (run (var 0) (var 1)) (var 2) ≐ GaussianScalarDeterminant.scalarDet (shiftedTable (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (returned_evaluation _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalCharacteristicPolynomial
