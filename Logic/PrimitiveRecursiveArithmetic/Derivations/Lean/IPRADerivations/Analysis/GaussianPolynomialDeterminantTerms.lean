import IPRADerivations.Foundations.RuntimePermutationWords
import IPRADerivations.Foundations.GuardedTotalization
import IPRADerivations.Analysis.GaussianRationalPolynomialProduct
import IPRADerivations.Analysis.GaussianRationalMonicReduction
import IPRADerivations.Analysis.GaussianRationalCoefficientScaling
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual polynomial products for numeric determinant words

A runtime Horner-style product loop reads M(digit_j,j), retaining every
polynomial coefficient. Numerical m, L, word, prefix and query point are
internal. Its coefficient recurrence is the actual bounded convolution and
its evaluator product law is derived by genuine quantifier-free induction.
Even inversion parity selects +1; odd parity selects -1, explicitly below.
This constructs terms, not multilinearity, alternation or determinant product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (singleton singleton_length singleton_evaluation evaluate_congr canonical_coefficients_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit parity)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cell (M r j : PTm n) : PTm n := entry (entry M r) j
def rowCells (M m L r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  length (cell (Syn.shift M) (Syn.shift r) (var 0)) ≐ succ (Syn.shift L))
@[simp] theorem subst_rowCells {l : ℕ} (σ : Fin n → PTm l) (M m L r : PTm n) :
    (rowCells M m L r).subst σ = rowCells (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ r) := by
  simp [rowCells,cell,Syn.subst_shift,Syn.shift_subst]
def tableShape (M m L : PTm n) : Fm PTm n := (length M ≐ m) ⋏
  (.all (lt (var 0) (Syn.shift m) ⟶ length (entry (Syn.shift M) (var 0)) ≐ Syn.shift m) ⋏
    .all (lt (var 0) (Syn.shift m) ⟶ rowCells (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0)))

def factor (M m w j : PTm n) : PTm n := cell M (digit m w j) j
def data (M m L w : PTm n) : PTm n := pairT M (pairT m (pairT L w))
def factorBody : PTm 2 := factor (fstT (var 1)) (fstT (sndT (var 1)))
  (sndT (sndT (sndT (var 1)))) (var 0)
def widthBody : PTm 1 := fstT (sndT (sndT (var 0)))
def stepBody : PTm 3 := GaussianRationalPolynomialProduct.product (var 1)
  (inst2 factorBody (var 0) (var 2)) (var 0*fstT (sndT (sndT (var 2)))) (fstT (sndT (sndT (var 2))))
def stageF : PR 2 := rec2 (singleton qone : PTm 1) stepBody
def stage (M m L w j : PTm n) : PTm n := ap2 stageF j (data M m L w)
def scalarBody : PTm 3 := qmul (var 1)
  (evaluate (inst2 factorBody (var 0) (fstT (var 2))) (sndT (var 2)))
def scalarF : PR 2 := rec2 (qone : PTm 1) scalarBody
def scalarProduct (M m L w z j : PTm n) : PTm n := ap2 scalarF j (pairT (data M m L w) z)
def signPoint (m w : PTm n) : PTm n :=
  Foundations.GuardedTotalization.sel (parity m w) (qnegative qone) qone
def term (M m L w : PTm n) : PTm n := scaled (stage M m L w m) (signPoint m w)

@[simp] theorem subst_cell {l : ℕ} (σ : Fin n → PTm l) (M r j : PTm n) :
    Syn.subst σ (cell M r j) = cell (Syn.subst σ M) (Syn.subst σ r) (Syn.subst σ j) := by simp [cell]
@[simp] theorem subst_tableShape {l : ℕ} (σ : Fin n → PTm l) (M m L : PTm n) :
    (tableShape M m L).subst σ = tableShape (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [tableShape,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_factor {l : ℕ} (σ : Fin n → PTm l) (M m w j : PTm n) :
    Syn.subst σ (factor M m w j) = factor (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ j) := by simp [factor]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (M m L w : PTm n) :
    Syn.subst σ (data M m L w) = data (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) := by simp [data]
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (stage M m L w j) = stage (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [stage]
@[simp] theorem subst_scalarProduct {l : ℕ} (σ : Fin n → PTm l) (M m L w z j : PTm n) :
    Syn.subst σ (scalarProduct M m L w z j) = scalarProduct (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ z) (Syn.subst σ j) := by simp [scalarProduct]
@[simp] theorem subst_signPoint {l : ℕ} (σ : Fin n → PTm l) (m w : PTm n) :
    Syn.subst σ (signPoint m w) = signPoint (Syn.subst σ m) (Syn.subst σ w) := by simp [signPoint]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (M m L w : PTm n) :
    Syn.subst σ (term M m L w) = term (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) := by simp [term]

theorem cell_length (M m L r j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell M r j) ≐ succ L := by
  have outer : Γ ⊢[PRAAx] lt r m ⟶ rowCells M m L r := by
    simpa only [Fm.subst_imp,subst_lt,subst_rowCells,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (Prf.andE₂ (Prf.andE₂ h)).allE r
  have gate : Γ ⊢[PRAAx] lt j m ⟶ length (cell M r j) ≐ succ L := by
    simpa only [rowCells,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,subst_cell,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using (Prf.impE outer hr).allE j
  exact .impE gate hj

theorem factor_length (M m L w j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] length (factor M m w j) ≐ succ L :=
  cell_length M m L _ j h (Foundations.RuntimePermutationWords.digit_bound m w j hj) hj

theorem factor_congr {M M' m m' w w' j j' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    factor M m w j ≐ factor M' m' w' j' := by
  ipra_congr (factor (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hM, hm, hw, hj]
theorem factor_body_at (M m L w j : PTm n) : Γ ⊢[PRAAx]
    inst2 factorBody j (data M m L w) ≐ factor M m w j := by
  simp only [factorBody,inst2,subst_factor,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) M (pairT m (pairT L w))
  have rest := (congrSnd tail).eqTrans (snd_pair m (pairT L w))
  exact factor_congr (fst_pair _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd rest).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem width_at (M m L w : PTm n) : Γ ⊢[PRAAx] Syn.subst ![data M m L w] widthBody ≐ L := by
  simpa only [widthBody,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,data] using
    (congrFst ((congrSnd (snd_pair (Γ := Γ) M (pairT m (pairT L w)))).eqTrans (snd_pair m (pairT L w)))).eqTrans (fst_pair L w)

theorem product_congr {P P' Q Q' N N' L L' : PTm n}
    (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx]
    GaussianRationalPolynomialProduct.product P Q N L ≐ GaussianRationalPolynomialProduct.product P' Q' N' L' := by
  ipra_congr (GaussianRationalPolynomialProduct.product (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hP, hQ, hN, hL]
theorem stage_congr {M M' m m' L L' w w' j j' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m') (hL : Γ ⊢[PRAAx] L ≐ L')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    stage M m L w j ≐ stage M' m' L' w' j' := by
  ipra_congr (stage (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hM, hm, hL, hw, hj]
theorem stage_zero (M m L w : PTm n) : Γ ⊢[PRAAx] stage M m L w zero ≐ singleton qone := by
  simpa only [stage,stageF,GaussianRationalMonicReduction.subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (singleton qone : PTm 1) stepBody (data M m L w)
theorem stage_succ (M m L w j : PTm n) : Γ ⊢[PRAAx] stage M m L w (succ j) ≐
    GaussianRationalPolynomialProduct.product (stage M m L w j) (factor M m w j) (j*L) L := by
  have e := rec2_succ (Γ := Γ) (singleton qone : PTm 1) stepBody j (data M m L w)
  simp only [stepBody,GaussianRationalPolynomialProduct.subst_product,subst_inst2,PTm.subst_mul,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  have hw : Γ ⊢[PRAAx] fstT (sndT (sndT (data M m L w))) ≐ L := by
    simpa only [widthBody,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero] using width_at M m L w
  exact e.eqTrans (product_congr (.eqRefl _) (factor_body_at _ _ _ _ _) (congrMul (.eqRefl _) hw) hw)

theorem stage_length (M m L w j : PTm n) : Γ ⊢[PRAAx] length (stage M m L w j) ≐ succ (j*L) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact (congrFst (stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0)).eqTrans
      ((congrFst (stage_zero _ _ _ _)).eqTrans ((singleton_length _).eqTrans (congrSucc ((congrMul Prf.hyp0 (.eqRefl L)).eqTrans (zero_mul _))).eqSymm))
  · exact (congrFst (stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0)).eqTrans
      ((congrFst (stage_succ _ _ _ _ _)).eqTrans
        ((GaussianRationalPolynomialProduct.product_length _ _ _ _).eqTrans (by
          have e := congrMul (Γ := (j ≐ succ (pred j)) :: Γ) Prf.hyp0 (.eqRefl L)
          apply withEq e
          intro he
          apply deriveNat
          ipra_simps
          rw [he]
          ring)))

theorem index_one_zero (i : PTm n) (hi : Γ ⊢[PRAAx] lt i one) : Γ ⊢[PRAAx] i ≐ zero :=
  (monus_zero i).eqSymm.eqTrans ((succ_monus_succ i zero).eqSymm.eqTrans hi)
theorem singleton_one_canonical : Γ ⊢[PRAAx] canonicalCoefficients (singleton (qone : PTm n)) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (singleton (qone : PTm n)))) :: Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] lt (var 0) (length (singleton (qone : PTm (n+1)))) := by
    simpa only [Δ,Syn.shift,GaussianRationalMonicReduction.subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
      (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (singleton (qone : PTm n)))))
  have hi : Δ ⊢[PRAAx] lt (var 0) one := lt_congr (.eqRefl _) (singleton_length qone) h
  have e : Δ ⊢[PRAAx] entry (singleton (qone : PTm (n+1))) (var 0) ≐ qone :=
    (entry_congr (.eqRefl (singleton qone)) (index_one_zero _ hi)).eqTrans (GaussianRationalMonicReduction.singleton_lookup _)
  simpa only [Δ,Syn.shift,GaussianRationalMonicReduction.subst_singleton,GaussianRationalSyntheticDivision.subst_qone] using
    (GaussianRationalHorner.canonical_congr e (qone_canonical (Γ := Δ)))

theorem stage_canonical (M m L w j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (stage M m L w j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact canonical_coefficients_congr
      ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_zero _ _ _ _)) singleton_one_canonical
  · exact canonical_coefficients_congr
      ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_succ _ _ _ _ _))
      (GaussianRationalPolynomialProduct.product_canonical _ _ _ _)

theorem scalar_zero (M m L w z : PTm n) : Γ ⊢[PRAAx] scalarProduct M m L w z zero ≐ qone := by
  simpa only [scalarProduct,scalarF,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (qone : PTm 1) scalarBody (pairT (data M m L w) z)
theorem scalar_succ (M m L w z j : PTm n) : Γ ⊢[PRAAx] scalarProduct M m L w z (succ j) ≐
    qmul (scalarProduct M m L w z j) (evaluate (factor M m w j) z) := by
  have e := rec2_succ (Γ := Γ) (qone : PTm 1) scalarBody j (pairT (data M m L w) z)
  simp only [scalarBody,GaussianRationalHorner.subst_qmul,GaussianRationalHorner.subst_evaluate,subst_inst2,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  exact e.eqTrans (qmul_congr (.eqRefl _) (evaluate_congr
    ((congrInst2 factorBody (.eqRefl _) (fst_pair _ _)).eqTrans (factor_body_at _ _ _ _ _)) (snd_pair _ _)))

def evaluationLaw (M m L w z j : PTm n) : Fm PTm n := le j m ⟶
  evaluate (stage M m L w j) z ≐ scalarProduct M m L w z j
@[simp] theorem subst_evaluationLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w z j : PTm n) :
    (evaluationLaw M m L w z j).subst σ = evaluationLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ w) (Syn.subst σ z) (Syn.subst σ j) := by simp [evaluationLaw]
theorem evaluation_zero (M m L w z : PTm n) : Γ ⊢[PRAAx]
    evaluate (stage M m L w zero) z ≐ scalarProduct M m L w z zero :=
  (evaluate_congr (stage_zero _ _ _ _) (.eqRefl _)).eqTrans
    ((singleton_evaluation _ _).eqTrans ((GaussianTranslatedNonconstant.recode_eq _ qone_canonical).eqTrans
      (scalar_zero _ _ _ _ _).eqSymm))
theorem evaluation_step (M m L w z j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt j m)
    (he : Γ ⊢[PRAAx] evaluate (stage M m L w j) z ≐ scalarProduct M m L w z j) : Γ ⊢[PRAAx]
    evaluate (stage M m L w (succ j)) z ≐ scalarProduct M m L w z (succ j) :=
  (evaluate_congr (stage_succ _ _ _ _ _) (.eqRefl _)).eqTrans
    ((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (stage_length _ _ _ _ _) (factor_length _ _ _ _ _ h hj)).eqTrans
      ((qmul_congr he (.eqRefl _)).eqTrans (scalar_succ _ _ _ _ _ _).eqSymm))

theorem stage_evaluation (M m L w z j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    evaluate (stage M m L w j) z ≐ scalarProduct M m L w z j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,subst_tableShape,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (evaluation_zero _ _ _ _ _)
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact evaluation_step _ _ _ _ _ _ hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have gate : Γ ⊢[PRAAx] evaluationLaw M m L w z j := by
    simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

/-- The stored coefficient recurrence is the genuine bounded convolution. -/
theorem stage_coefficient_succ (M m L w j s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ j*L)) : Γ ⊢[PRAAx]
    entry (stage M m L w (succ j)) s ≐ GaussianRationalPolynomialProduct.coefficient
      (stage M m L w j) (factor M m w j) L (succ (j*L)) s :=
  (entry_congr (stage_succ _ _ _ _ _) (.eqRefl _)).eqTrans
    (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _
      (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ j*L ≐ j*L+L) hs))

/-- These branch equations fix the determinant sign convention before any
polynomial signing: even is +1 and odd is -1. -/
theorem sign_even (m w : PTm n) (h : Γ ⊢[PRAAx] parity m w ≐ zero) : Γ ⊢[PRAAx] signPoint m w ≐ qone :=
  Foundations.GuardedTotalization.sel_zero h
theorem sign_odd (m w : PTm n) (h : Γ ⊢[PRAAx] parity m w ≐ one) : Γ ⊢[PRAAx] signPoint m w ≐ qnegative qone :=
  Foundations.GuardedTotalization.sel_one h
theorem sign_canonical (m w : PTm n) : Γ ⊢[PRAAx] canonical (signPoint m w) :=
  .orE (Foundations.RuntimePermutationWords.parity_cases m w)
    (GaussianRationalHorner.canonical_congr (sign_even _ _ Prf.hyp0) qone_canonical)
    (GaussianRationalHorner.canonical_congr (sign_odd _ _ Prf.hyp0) (qnegative_canonical _))
theorem term_length (M m L w : PTm n) : Γ ⊢[PRAAx] length (term M m L w) ≐ succ (m*L) :=
  (scaled_length _ _).eqTrans (stage_length _ _ _ _ _)
theorem scaled_canonical (C r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (scaled C r) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (scaled C r))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (scaled (Syn.shift C) (Syn.shift r))) := by
    simpa only [Δ,Syn.shift,GaussianRationalCoefficientScaling.subst_scaled] using
      (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (scaled C r))))
  have bound : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift C)) :=
    lt_congr (.eqRefl _) (scaled_length (Syn.shift C) (Syn.shift r)) hi
  simpa only [Δ,Syn.shift,GaussianRationalCoefficientScaling.subst_scaled] using
    GaussianRationalCoefficientScaling.scaled_entry_canonical (Syn.shift C) (Syn.shift r) (var 0) bound

theorem term_canonical (M m L w : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (term M m L w) :=
  scaled_canonical _ _

theorem term_coefficient (M m L w s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (term M m L w) s ≐ qmul (signPoint m w) (entry (stage M m L w m) s) :=
  scaled_lookup _ _ _ (lt_congr (.eqRefl _) (stage_length _ _ _ _ _).eqSymm ((succ_monus_succ _ _).eqTrans hs))
theorem term_evaluation (M m L w z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (term M m L w) z ≐ qmul (signPoint m w) (scalarProduct M m L w z m) :=
  (evaluation_linearity _ _ _).eqTrans (qmul_congr (.eqRefl _) (stage_evaluation _ _ _ _ _ _ h (le_refl _)))

theorem empty_term_evaluation (M L w z : PTm n) : Γ ⊢[PRAAx] evaluate (term M zero L w) z ≐ qone :=
  (evaluation_linearity _ _ _).eqTrans
    ((qmul_congr (sign_even _ _ (Foundations.RuntimePermutationWords.parity_zero _))
      ((evaluate_congr (stage_zero _ _ _ _) (.eqRefl _)).eqTrans
        ((singleton_evaluation _ _).eqTrans (GaussianTranslatedNonconstant.recode_eq _ qone_canonical)))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ qone_canonical))


theorem one_mul_canonical (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] qmul qone q ≐ q :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ hq)
theorem factor_one_zero (M w : PTm n) : Γ ⊢[PRAAx] factor M one w zero ≐ cell M zero zero :=
  entry_congr (entry_congr (.eqRefl _) (index_one_zero _
    (Foundations.RuntimePermutationWords.digit_bound one w zero (le_refl one)))) (.eqRefl _)
theorem singleton_term_evaluation (M L w z : PTm n) (h : Γ ⊢[PRAAx] tableShape M one L) : Γ ⊢[PRAAx]
    evaluate (term M one L w) z ≐ evaluate (cell M zero zero) z := by
  have e : Γ ⊢[PRAAx] scalarProduct M one L w z one ≐ evaluate (cell M zero zero) z :=
    (scalar_succ _ _ _ _ _ zero).eqTrans
      ((qmul_congr (scalar_zero _ _ _ _ _) (evaluate_congr (factor_one_zero _ _) (.eqRefl _))).eqTrans
        (one_mul_canonical _ (GaussianRationalHorner.horner_canonical _ _ _)))
  exact (term_evaluation _ _ _ _ _ h).eqTrans
    ((qmul_congr (sign_even _ _ (Foundations.RuntimePermutationWords.parity_one _)) e).eqTrans
      (one_mul_canonical _ (GaussianRationalHorner.horner_canonical _ _ _)))

/-! Actual programs expose unsigned and signed polynomial codes together
with their sign. The query z is used only by the evaluator certificate. -/
def output (M m L w : PTm n) : PTm n := pairT (term M m L w) (pairT (stage M m L w m) (signPoint m w))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (M m L w : PTm n) : PTm n := app outputF ![M,m,L,w]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L w : PTm n) :
    Syn.subst σ (output M m L w) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L w : PTm n) :
    Syn.subst σ (run M m L w) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (M m L w : PTm n) : Γ ⊢[PRAAx] run M m L w ≐ output M m L w := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![M,m,L,w]
theorem returned_term (M m L w : PTm n) : Γ ⊢[PRAAx] fstT (run M m L w) ≐ term M m L w :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_product (M m L w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run M m L w)) ≐ stage M m L w m :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sign (M m L w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run M m L w)) ≐ signPoint m w :=
  (congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_term_length (M m L w : PTm n) : Γ ⊢[PRAAx] length (fstT (run M m L w)) ≐ succ (m*L) :=
  (congrFst (returned_term _ _ _ _)).eqTrans (term_length _ _ _ _)
theorem returned_term_canonical (M m L w : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (fstT (run M m L w)) :=
  canonical_coefficients_congr (returned_term _ _ _ _) (term_canonical _ _ _ _)
theorem returned_term_evaluation (M m L w z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (fstT (run M m L w)) z ≐ qmul (signPoint m w) (scalarProduct M m L w z m) :=
  (evaluate_congr (returned_term _ _ _ _) (.eqRefl _)).eqTrans (term_evaluation _ _ _ _ _ h)

theorem determinant_sign_branches_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((parity (var 0) (var 1) ≐ zero ⟶ signPoint (var 0) (var 1) ≐ qone) ⋏
      (parity (var 0) (var 1) ≐ one ⟶ signPoint (var 0) (var 1) ≐ qnegative qone)) :=
  closeUniv 2 (.andI (.impI (sign_even _ _ Prf.hyp0)) (.impI (sign_odd _ _ Prf.hyp0)))
theorem actual_polynomial_word_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (term (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1*var 2)) ⋏
      canonicalCoefficients (term (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (term_length _ _ _ _) (term_canonical _ _ _ _))
theorem actual_word_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (succ (var 4)*var 2) ⟶
      entry (stage (var 0) (var 1) (var 2) (var 3) (succ (var 4))) (var 5) ≐
        GaussianRationalPolynomialProduct.coefficient (stage (var 0) (var 1) (var 2) (var 3) (var 4))
          (factor (var 0) (var 1) (var 3) (var 4)) (var 2) (succ (var 4*var 2)) (var 5)) :=
  closeUniv 6 (.impI (stage_coefficient_succ _ _ _ _ _ _ Prf.hyp0))
theorem actual_polynomial_word_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (tableShape (var 0) (var 1) (var 2) ⟶ le (var 5) (var 1) ⟶
      evaluate (stage (var 0) (var 1) (var 2) (var 3) (var 5)) (var 4) ≐
        scalarProduct (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (stage_evaluation _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem signed_polynomial_word_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶
      evaluate (term (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qmul (signPoint (var 1) (var 3)) (scalarProduct (var 0) (var 1) (var 2) (var 3) (var 4) (var 1))) :=
  closeUniv 5 (.impI (term_evaluation _ _ _ _ _ Prf.hyp0))
theorem actual_polynomial_word_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_polynomial_word_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶
      evaluate (fstT (run (var 0) (var 1) (var 2) (var 3))) (var 4) ≐
        qmul (signPoint (var 1) (var 3)) (scalarProduct (var 0) (var 1) (var 2) (var 3) (var 4) (var 1))) :=
  closeUniv 5 (.impI (returned_term_evaluation _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms
