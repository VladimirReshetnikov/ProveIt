import IPRADerivations.Analysis.Polynomials.Representation.GaussianPolynomialConstantInjection
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual arbitrary-high-Y remainder fold for a monic plane equation

Every incoming row is an ORIGINAL X-polynomial. The actual recursor shifts
the current low-Y remainder by the existing polynomial companion and adds
that original row at constant Y. Dynamic numerical X width is a+j*c.
The guarded scalar-query QF invariant derives preservation on the original
monic curve. This constructs the remainder; the full polynomial quotient
and coefficient identity H=QF+R remain a separate required extension.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialMonicHornerReduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate horner hornerF qzero qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr canonicalCoefficients)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at companion values values_length values_lookup monicValues)
open GaussianPolynomialMultiplicationMatrix (stored storedSyntax formula_stored stored_congr)
open GaussianPolynomialConstantInjection (inject inject_stored inject_evaluation fields)
open GaussianRationalPolynomialBuffers (zeros zeros_length zeros_lookup zeros_evaluation)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (a c j : PTm n) : PTm n := a+j*c
def zeroRows (m a : PTm n) : PTm n := sequence (var 1 : PTm 2) m (zeros (succ a))
def data (F H m a c : PTm n) : PTm n := GaussianPolynomialMonicCompanion.data F H m a c
def advance (F H m a c j R : PTm n) : PTm n :=
  inject (companion F R m (width a c j) c) (entry H j) m a (succ j*c)
def advanceF : PR 7 := PTm.toPR (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def initial : PTm 1 := zeroRows (fields (var 0) 2) (fields (var 0) 3)
def stepBody : PTm 3 := app advanceF ![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,fields (var 2) 3,fields (var 2) 4,var 0,var 1]
def stageF : PR 2 := rec2 initial stepBody
def stage (F H m a c j : PTm n) : PTm n := ap2 stageF j (data F H m a c)

@[simp] theorem subst_width {k : ℕ} (σ : Fin n → PTm k) (a c j : PTm n) :
    Syn.subst σ (width a c j) = width (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [width]
@[simp] theorem subst_zeroRows {k : ℕ} (σ : Fin n → PTm k) (m a : PTm n) :
    Syn.subst σ (zeroRows m a) = zeroRows (Syn.subst σ m) (Syn.subst σ a) := by simp [zeroRows]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (F H m a c : PTm n) :
    Syn.subst σ (data F H m a c) = data (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [data]
@[simp] theorem subst_advance {k : ℕ} (σ : Fin n → PTm k) (F H m a c j R : PTm n) :
    Syn.subst σ (advance F H m a c j R) = advance (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a)
      (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ R) := by simp [advance]
@[simp] theorem subst_stage {k : ℕ} (σ : Fin n → PTm k) (F H m a c j : PTm n) :
    Syn.subst σ (stage F H m a c j) = stage (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [stage]

theorem tuple_seven_fifth {α : Type} (a b c d e f g : α) : ![a,b,c,d,e,f,g] (5 : Fin 7) = f := rfl
theorem tuple_seven_last {α : Type} (a b c d e f g : α) : ![a,b,c,d,e,f,g] (6 : Fin 7) = g := rfl
theorem data_fields (F H m a c : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (data F H m a c) i ≐ ![F,H,m,a,c] i :=
  GaussianPolynomialConstantInjection.fields_at _ _ _ _ _ i
theorem zero_rows_length (m a : PTm n) : Γ ⊢[PRAAx] length (zeroRows m a) ≐ m := sequence_length _ _ _
theorem zero_rows_lookup (m a r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (zeroRows m a) r ≐ zeros (succ a) := by simpa only [zeroRows,inst2,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_zero] using sequence_decode (Γ := Γ) (var 1 : PTm 2) (x := zeros (succ a)) hr
theorem zero_rows_congr {m m' a a' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    zeroRows m a ≐ zeroRows m' a' := by
  ipra_congr (zeroRows (var 0) (var 1) : PTm 2) with [hm, ha]
theorem advance_program (F H m a c j R : PTm n) : Γ ⊢[PRAAx] app advanceF ![F,H,m,a,c,j,R] ≐ advance F H m a c j R := by
  simpa [advanceF] using toPR_eq (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![F,H,m,a,c,j,R]
theorem advance_congr {F F' H H' m m' a a' c c' j j' R R' : PTm n}
    (hF : Γ ⊢[PRAAx] F ≐ F') (hH : Γ ⊢[PRAAx] H ≐ H') (hm : Γ ⊢[PRAAx] m ≐ m') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hc : Γ ⊢[PRAAx] c ≐ c') (hj : Γ ⊢[PRAAx] j ≐ j') (hR : Γ ⊢[PRAAx] R ≐ R') : Γ ⊢[PRAAx]
    advance F H m a c j R ≐ advance F' H' m' a' c' j' R' := by
  simpa only [subst_advance,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,tuple_seven_fifth,tuple_seven_last,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![F,H,m,a,c,j,R]) (σ' := ![F',H',m',a',c',j',R'])
      (fun i => by fin_cases i <;> simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']; exact hF; exact hH; exact hm; exact ha; exact hc; exact hj; exact hR)
theorem stage_zero (F H m a c : PTm n) : Γ ⊢[PRAAx] stage F H m a c zero ≐ zeroRows m a := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data F H m a c)
  simp only [initial,subst_zeroRows,GaussianPolynomialConstantInjection.subst_fields,Syn.subst_var,Syn.inst_zero] at e
  exact e.eqTrans (zero_rows_congr (data_fields _ _ _ _ _ 2) (data_fields _ _ _ _ _ 3))
theorem stage_succ (F H m a c j : PTm n) : Γ ⊢[PRAAx] stage F H m a c (succ j) ≐ advance F H m a c j (stage F H m a c j) := by
  have e := rec2_succ (Γ := Γ) initial stepBody j (data F H m a c)
  have vector : (fun i => Syn.subst ![j,stage F H m a c j,data F H m a c]
      ((![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,fields (var 2) 3,fields (var 2) 4,var 0,var 1] : Fin 7 → PTm 3) i)) =
      ![fields (data F H m a c) 0,fields (data F H m a c) 1,fields (data F H m a c) 2,
        fields (data F H m a c) 3,fields (data F H m a c) 4,j,stage F H m a c j] := by
    funext i
    fin_cases i <;> simp
  change Γ ⊢[PRAAx] stage F H m a c (succ j) ≐ app advanceF
    (fun i => Syn.subst ![j,stage F H m a c j,data F H m a c]
      ((![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,fields (var 2) 3,fields (var 2) 4,var 0,var 1] : Fin 7 → PTm 3) i)) at e
  rw [vector] at e
  exact e.eqTrans ((advance_program _ _ _ _ _ _ _).eqTrans
    (advance_congr (data_fields F H m a c 0) (data_fields F H m a c 1) (data_fields F H m a c 2)
      (data_fields F H m a c 3) (data_fields F H m a c 4) (.eqRefl _) (.eqRefl _)))

theorem zero_rows_stored (m a : PTm n) : Γ ⊢[PRAAx] stored (zeroRows m a) m a := by
  refine .andI (zero_rows_length _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_zeroRows,length] using (congrFst
      (zero_rows_lookup (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)).eqTrans (zeros_length _)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_zeroRows] using GaussianRationalMonicReduction.canonical_coefficients_congr
      (zero_rows_lookup (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0) (GaussianRationalMonicReduction.zeros_canonical _)

theorem stage_stored (F H m a c j : PTm n) : Γ ⊢[PRAAx] stored (stage F H m a c j) m (width a c j) := by
  let S := storedSyntax (stage (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0))
    (Syn.shift m) (width (Syn.shift a) (Syn.shift c) (var 0))
  have all : Γ ⊢[PRAAx] .all (Foundations.BoundedSyntax.formula S) := by
    apply Foundations.BoundedSyntaxInduction.induction
    · simp only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_stage,subst_width,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact stored_congr (stage_zero _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring) (zero_rows_stored _ _)
    · simp only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_stage,subst_width,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact stored_congr (stage_succ _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (inject_stored _ _ _ _ _)
  simpa only [S,formula_stored,GaussianPolynomialMultiplicationMatrix.subst_stored,subst_stage,subst_width,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem stage_length (F H m a c j : PTm n) : Γ ⊢[PRAAx] length (stage F H m a c j) ≐ m := .andE₁ (stage_stored _ _ _ _ _ _)
theorem stage_shape (F H m a c j : PTm n) : Γ ⊢[PRAAx] rowShape (stage F H m a c j) m (width a c j) := .andE₁ (.andE₂ (stage_stored _ _ _ _ _ _))

theorem zero_rows_evaluation (m a x y : PTm n) : Γ ⊢[PRAAx] evaluate (values (zeroRows m a) m x) y ≐ qzero := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      entry (Syn.shift (values (zeroRows m a) m x)) (var 0) ≐ entry (Syn.shift (zeros m)) (var 0)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e := (values_lookup (Γ := Δ) (zeroRows (Syn.shift m) (Syn.shift a)) (Syn.shift m) (Syn.shift x) (var 0) Prf.hyp0).eqTrans
      ((GaussianPolynomialMonicCompanion.evaluation_congr (zero_rows_lookup _ _ _ Prf.hyp0) (.eqRefl _)).eqTrans
        ((zeros_evaluation _ _).eqTrans (zeros_lookup _ _ Prf.hyp0).eqSymm))
    simpa only [Δ,Syn.shift,GaussianPolynomialMonicCompanion.subst_values,subst_zeroRows,GaussianRationalPolynomialBuffers.subst_zeros] using e
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl y)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ _ m m entries (le_refl _)).eqTrans
      ((congrAp3 hornerF (zeros_length m).eqSymm (.eqRefl _) (.eqRefl y)).eqTrans (zeros_evaluation _ _)))

theorem advance_evaluation (F H m a c j R x y : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hR : Γ ⊢[PRAAx] rowShape R m (width a c j))
    (hIncoming : Γ ⊢[PRAAx] length (entry H j) ≐ succ a)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (values (advance F H m a c j R) m x) y ≐
      qadd (qmul (evaluate (values R m x) y) y) (evaluate (entry H j) x) := by
  have shaped : Γ ⊢[PRAAx] stored (companion F R m (width a c j) c) m (a+succ j*c) :=
    stored_congr (.eqRefl _) (.eqRefl _) (by unfold width; ipra_ring)
      (GaussianPolynomialMultiplicationMatrix.companion_stored _ _ _ _ _)
  have curve := GaussianPolynomialMonicCompanion.curve_step F R m (width a c j) c x y hm hF hR hCurve
  exact (inject_evaluation _ _ _ _ _ _ _ hm (.andE₁ (.andE₂ shaped)) hIncoming).eqTrans
    (qadd_congr (curve.eqSymm.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _)) (.eqRefl _))

def prefixLaw (F H m a c L x y j : PTm n) : Fm PTm n := le j L ⟶
  evaluate (values (stage F H m a c j) m x) y ≐ horner (values H L x) y j
@[simp] theorem subst_prefixLaw {k : ℕ} (σ : Fin n → PTm k) (F H m a c L x y j : PTm n) :
    (prefixLaw F H m a c L x y j).subst σ = prefixLaw (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ j) := by simp [prefixLaw]

theorem prefix_evaluation (F H m a c L x y j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    evaluate (values (stage F H m a c j) m x) y ≐ horner (values H L x) y j := by
  have hms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hF.shift
  have hHs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (Syn.shift L) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hH.shift
  have hCs : Γ.map Fm.shift ⊢[PRAAx] evaluate (monicValues (Syn.shift F) (Syn.shift m) (Syn.shift x)) (Syn.shift y) ≐ qzero := by
    simpa [Fm.shift,Syn.shift] using hCurve.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c)
      (Syn.shift L) (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianPolynomialMonicCompanion.evaluation_congr
        (GaussianPolynomialMonicCompanion.values_congr (stage_zero _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
          ((zero_rows_evaluation _ _ _ _).eqTrans (GaussianRationalHorner.horner_zero _ _).eqSymm)).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift L) :: prefixLaw (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c)
        (Syn.shift L) (Syn.shift x) (Syn.shift y) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] evaluate (values (stage (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0))
          (Syn.shift m) (Syn.shift x)) (Syn.shift y) ≐ horner (values (Syn.shift H) (Syn.shift L) (Syn.shift x)) (Syn.shift y) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have incoming := row_shape_at (Γ := Δ) (Syn.shift H) (Syn.shift L) (Syn.shift a) (var 0) hHs.wk.wk Prf.hyp0
      have step := (GaussianPolynomialMonicCompanion.evaluation_congr
        (GaussianPolynomialMonicCompanion.values_congr (stage_succ (Γ := Δ) _ _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
          (advance_evaluation _ _ _ _ _ _ _ _ _ hms.wk.wk hFs.wk.wk (stage_shape _ _ _ _ _ _) incoming hCs.wk.wk)
      exact step.eqTrans ((qadd_congr (qmul_congr ih (.eqRefl _)) (values_lookup _ _ _ _ Prf.hyp0).eqSymm).eqTrans
        (GaussianRationalHorner.horner_succ _ _ _).eqSymm)
  have queried : Γ ⊢[PRAAx] prefixLaw F H m a c L x y j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE queried hj

def input (F H m a c N : PTm n) : Fm PTm n := le one m ⋏ ((length F ≐ m) ⋏
  (rowShape F m c ⋏ ((length H ≐ succ N) ⋏ rowShape H (succ N) a)))
def remainder (F H m a c N : PTm n) : PTm n := stage F H m a c (succ N)
def originalValue (H x y : PTm n) : PTm n := evaluate (values H (length H) x) y
@[simp] theorem subst_input {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    (input F H m a c N).subst σ = input (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_remainder {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (remainder F H m a c N) = remainder (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [remainder]
@[simp] theorem subst_originalValue {k : ℕ} (σ : Fin n → PTm k) (H x y : PTm n) :
    Syn.subst σ (originalValue H x y) = originalValue (Syn.subst σ H) (Syn.subst σ x) (Syn.subst σ y) := by simp [originalValue]
theorem remainder_stored (F H m a c N : PTm n) : Γ ⊢[PRAAx] stored (remainder F H m a c N) m (width a c (succ N)) := stage_stored _ _ _ _ _ _
theorem reduction_evaluation (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (values (remainder F H m a c N) m x) y ≐ originalValue H x y := by
  have hm := Prf.andE₁ h
  have hF := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hLen := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hH := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact (prefix_evaluation F H m a c (succ N) x y (succ N) hm hF hH hCurve (le_refl _)).eqTrans
    ((congrAp3 hornerF (values_length H (succ N) x).eqSymm (.eqRefl _) (.eqRefl y)).eqTrans
      (GaussianPolynomialMonicCompanion.evaluation_congr
        (GaussianPolynomialMonicCompanion.values_congr (.eqRefl H) hLen.eqSymm (.eqRefl x)) (.eqRefl y)))
theorem original_zero_iff (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    Fm.iff (originalValue H x y ≐ qzero) (evaluate (values (remainder F H m a c N) m x) y ≐ qzero) := by
  have e := reduction_evaluation F H m a c N x y h hCurve
  exact .andI (.impI (e.wk.eqTrans Prf.hyp0)) (.impI (e.wk.eqSymm.eqTrans Prf.hyp0))

def remainderF : PR 6 := PTm.toPR (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (F H m a c N : PTm n) : PTm n := app remainderF ![F,H,m,a,c,N]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (run F H m a c N) = run (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (F H m a c N : PTm n) : Γ ⊢[PRAAx] run F H m a c N ≐ remainder F H m a c N := by
  simpa [run,remainderF] using toPR_eq (Γ := Γ) (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,H,m,a,c,N]
theorem returned_stored (F H m a c N : PTm n) : Γ ⊢[PRAAx] stored (run F H m a c N) m (width a c (succ N)) :=
  stored_congr (program_at _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (remainder_stored _ _ _ _ _ _)
theorem returned_evaluation (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (values (run F H m a c N) m x) y ≐ originalValue H x y :=
  (GaussianPolynomialMonicCompanion.evaluation_congr
    (GaussianPolynomialMonicCompanion.values_congr (program_at _ _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
      (reduction_evaluation _ _ _ _ _ _ _ _ h hCurve)

theorem actual_zero_rows_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (values (zeroRows (var 0) (var 1)) (var 0) (var 2)) (var 3) ≐ qzero) := closeUniv 4 (zero_rows_evaluation _ _ _ _)
theorem actual_monic_prefix_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stored (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (width (var 3) (var 4) (var 5))) :=
  closeUniv 6 (stage_stored _ _ _ _ _ _)
theorem actual_high_y_prefix_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 5) (var 3) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶ le (var 8) (var 5) ⟶
        evaluate (values (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 8)) (var 2) (var 6)) (var 7) ≐
          horner (values (var 1) (var 5) (var 6)) (var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI
    (prefix_evaluation _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_high_y_remainder_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        evaluate (values (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6)) (var 7) ≐
          originalValue (var 1) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (reduction_evaluation _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_high_y_original_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        Fm.iff (originalValue (var 1) (var 6) (var 7) ≐ qzero)
          (evaluate (values (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6)) (var 7) ≐ qzero)) :=
  closeUniv 8 (.impI (.impI (original_zero_iff _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_high_y_remainder_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_high_y_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stored (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (width (var 3) (var 4) (succ (var 5)))) :=
  closeUniv 6 (returned_stored _ _ _ _ _ _)
theorem actual_returned_high_y_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        evaluate (values (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6)) (var 7) ≐
          originalValue (var 1) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (returned_evaluation _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialMonicHornerReduction
