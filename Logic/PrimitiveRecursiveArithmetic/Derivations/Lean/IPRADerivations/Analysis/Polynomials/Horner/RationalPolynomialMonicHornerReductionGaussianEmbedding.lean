import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialConstantInjectionGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.CompanionMatrices.RationalPolynomialMultiplicationMatrixGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Horner.GaussianPolynomialMonicHornerReduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original rational arbitrary-high-Y remainder

A numerical recursor performs original rational polynomial companion steps
and injects each original coefficient row at constant Y. Its X width is
exactly a+j*c. A compiled bounded QF coefficient invariant derives transport
to the existing Gaussian remainder, and hence actual original rational
bivariate evaluation equality on the original monic curve. The full original
quotient and coefficient reconstruction H=QF+R remain a separate obligation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialMonicHornerReductionGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (zeros zeros_length embeddedEntries)
open RationalPolynomialMonicCompanionGaussianEmbedding (companion rowsEmbedded row_embedded_at)
open RationalPolynomialConstantInjectionGaussianEmbedding (inject fields)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open RationalPolynomialMultiplicationMatrixGaussianEmbedding (pairedRows paired_rows_congr rowShapeSyntax rowsEmbeddedSyntax)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
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
  RationalPolynomialConstantInjectionGaussianEmbedding.fields_at _ _ _ _ _ i
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
  simp only [initial,subst_zeroRows,RationalPolynomialConstantInjectionGaussianEmbedding.subst_fields,Syn.subst_var] at e
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

def targetStage (F H m a c L j : PTm n) : PTm n := GaussianPolynomialMonicHornerReduction.stage
  (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix H L (succ a)) m a c j
@[simp] theorem subst_targetStage {k : ℕ} (σ : Fin n → PTm k) (F H m a c L j : PTm n) :
    Syn.subst σ (targetStage F H m a c L j) = targetStage (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ j) := by simp [targetStage]

theorem zero_rows_profile (m a : PTm n) : Γ ⊢[PRAAx]
    pairedRows (zeroRows m a) (GaussianPolynomialMonicHornerReduction.zeroRows m a) m a := by
  refine .andI (.allI (.impI ?_)) (.allI (.impI ?_))
  · simpa only [Syn.shift,subst_zeroRows,ConciseIPRA.PTm.subst_succ,length] using
      (congrFst (zero_rows_lookup (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)).eqTrans (zeros_length _)
  · let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e := RationalPolynomialMonicCompanionGaussianEmbedding.embedded_congr
      (zero_rows_lookup (Syn.shift m) (Syn.shift a) (var 0) (Γ := Δ) Prf.hyp0).eqSymm
      (GaussianPolynomialMonicHornerReduction.zero_rows_lookup _ _ _ Prf.hyp0).eqSymm
      (RationalPolynomialBuffersGaussianEmbedding.zeros_embedded_entries (succ (Syn.shift a)))
    simpa only [Δ,Syn.shift,subst_zeroRows,GaussianPolynomialMonicHornerReduction.subst_zeroRows,ConciseIPRA.PTm.subst_succ] using e

def profile (F H m a c L j : PTm n) : Fm PTm n := le j L ⟶
  pairedRows (stage F H m a c j) (targetStage F H m a c L j) m (width a c j)
@[simp] theorem subst_profile {k : ℕ} (σ : Fin n → PTm k) (F H m a c L j : PTm n) :
    (profile F H m a c L j).subst σ = profile (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ L) (Syn.subst σ j) := by simp [profile]

theorem profile_base (F H m a c L : PTm n) : Γ ⊢[PRAAx] profile F H m a c L zero := by
  refine .impI ?_
  exact paired_rows_congr (stage_zero _ _ _ _ _).eqSymm (GaussianPolynomialMonicHornerReduction.stage_zero _ _ _ _ _).eqSymm
    (by unfold width; ipra_ring) (zero_rows_profile _ _)

theorem profile_step (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a)
    (ih : Γ ⊢[PRAAx] profile F H m a c L j) : Γ ⊢[PRAAx] profile F H m a c L (succ j) := by
  refine .impI ?_
  let Δ := le (succ j) L :: Γ
  have before : Δ ⊢[PRAAx] pairedRows (stage F H m a c j) (targetStage F H m a c L j) m (width a c j) :=
    .impE ih.wk (le_trans (le_succ_self _) Prf.hyp0)
  have ci : Δ ⊢[PRAAx] RationalPolynomialMonicCompanionGaussianEmbedding.transportInput
      F (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (stage F H m a c j) (targetStage F H m a c L j) m (width a c j) c :=
    .andI hm.wk (.andI hF.wk (.andI (RationalBivariateGaussianEmbedding.embedded_row_shape F m c)
      (.andI (.andE₁ before) (.andI (GaussianPolynomialMonicHornerReduction.stage_shape _ _ _ _ _ _)
        (.andI (RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _) (.andE₂ before))))))
  have cp : Δ ⊢[PRAAx] pairedRows (companion F (stage F H m a c j) m (width a c j) c)
      (GaussianPolynomialMonicCompanion.companion (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
        (targetStage F H m a c L j) m (width a c j) c) m (a+succ j*c) :=
    paired_rows_congr (.eqRefl _) (.eqRefl _) (by unfold width; ipra_ring)
      (.andI (RationalPolynomialMonicCompanionGaussianEmbedding.companion_row_shape _ _ _ _ _)
        (RationalPolynomialMonicCompanionGaussianEmbedding.companion_rows_embedded _ _ _ _ _ _ _ ci))
  have sourceRow := row_shape_at (Γ := Δ) H L a j hH.wk Prf.hyp0
  have targetRow := RationalBivariateGaussianEmbedding.embedded_row_length H L (succ a) j (Γ := Δ) Prf.hyp0
  have inputRow := RationalBivariateGaussianEmbedding.row_embedding H L (succ a) j (Γ := Δ) Prf.hyp0
  have out := RationalPolynomialConstantInjectionGaussianEmbedding.inject_rows_embedded
    (companion F (stage F H m a c j) m (width a c j) c)
    (GaussianPolynomialMonicCompanion.companion (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
      (targetStage F H m a c L j) m (width a c j) c)
    (entry H j) (entry (RationalRowSpanGaussianEmbedding.matrix H L (succ a)) j) m a (succ j*c)
    sourceRow targetRow (.andE₂ cp) inputRow
  exact paired_rows_congr (stage_succ _ _ _ _ _ _).eqSymm (GaussianPolynomialMonicHornerReduction.stage_succ _ _ _ _ _ _).eqSymm
    (.eqRefl _) (.andI (RationalPolynomialConstantInjectionGaussianEmbedding.inject_shape _ _ _ _ _) out)

def profileSyntax (F H m a c L j : PTm n) : BFm n := .imp (.le j L) (.and
  (rowShapeSyntax (stage F H m a c j) m (width a c j))
  (rowsEmbeddedSyntax (stage F H m a c j) (targetStage F H m a c L j) m (width a c j)))
theorem profile_formula (F H m a c L j : PTm n) : formula (profileSyntax F H m a c L j) = profile F H m a c L j := rfl

theorem stage_profile (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    pairedRows (stage F H m a c j) (targetStage F H m a c L j) m (width a c j) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hF.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift H) (Syn.shift L) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hH.shift
  let S := profileSyntax (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (var 0)
  have all : Γ ⊢[PRAAx] .all (profile (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift L) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact profile_base _ _ _ _ _ _
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact profile_step _ _ _ _ _ _ _ ms.wk fs.wk hs.wk Prf.hyp0
  have p : Γ ⊢[PRAAx] profile F H m a c L j := by
    simpa only [subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE p hj

theorem stage_shape (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    rowShape (stage F H m a c j) m (width a c j) := .andE₁ (stage_profile _ _ _ _ _ _ _ hm hF hH hj)

theorem stage_rows_embedded (F H m a c L j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hH : Γ ⊢[PRAAx] rowShape H L a) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    rowsEmbedded (stage F H m a c j) (targetStage F H m a c L j) m (width a c j) := .andE₂ (stage_profile _ _ _ _ _ _ _ hm hF hH hj)

theorem stage_length (F H m a c j : PTm n) : Γ ⊢[PRAAx] length (stage F H m a c j) ≐ m := by
  have all : Γ ⊢[PRAAx] .all (length (stage (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)) ≐ Syn.shift m) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_stage,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (stage_zero _ _ _ _ _)).eqTrans (zero_rows_length _ _)
    · simp only [Fm.subst_eq,subst_length,subst_stage,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (stage_succ _ _ _ _ _ _)).eqTrans (RationalPolynomialConstantInjectionGaussianEmbedding.inject_length _ _ _ _ _)
  simpa only [Fm.subst_eq,subst_length,subst_stage,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem row_shape_congr {A A' m m' b b' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hm : Γ ⊢[PRAAx] m ≐ m') (hb : Γ ⊢[PRAAx] b ≐ b') (h : Γ ⊢[PRAAx] rowShape A m b) : Γ ⊢[PRAAx] rowShape A' m' b' := by
  have out := Prf.eqSubst (Γ := Γ) (rowShape (var 0) (var 1) (var 2) : Fm PTm 3)
    ![A,m,b] ![A',m',b'] (fun i => by fin_cases i; exact hA; exact hm; exact hb) (by simpa using h)
  simpa using out

def computedShapeSyntax (F H m a c j : PTm n) : BFm n := rowShapeSyntax (stage F H m a c j) m (width a c j)
theorem computed_shape_formula (F H m a c j : PTm n) : formula (computedShapeSyntax F H m a c j) = rowShape (stage F H m a c j) m (width a c j) := rfl
theorem stage_computed_shape (F H m a c j : PTm n) : Γ ⊢[PRAAx] rowShape (stage F H m a c j) m (width a c j) := by
  let S := computedShapeSyntax (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)
  have all : Γ ⊢[PRAAx] .all (formula S) := by
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_stage,subst_width,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact row_shape_congr (stage_zero _ _ _ _ _).eqSymm (.eqRefl _) (by unfold width; ipra_ring) (.andE₁ (zero_rows_profile _ _))
    · simp only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_stage,subst_width,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact row_shape_congr (stage_succ _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (RationalPolynomialConstantInjectionGaussianEmbedding.inject_shape _ _ _ _ _)
  simpa only [S,computed_shape_formula,GaussianPolynomialMonicCompanion.subst_rowShape,subst_stage,subst_width,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def input (F H m a c N : PTm n) : Fm PTm n := le one m ⋏ ((length F ≐ m) ⋏
  (rowShape F m c ⋏ ((length H ≐ succ N) ⋏ rowShape H (succ N) a)))
def remainder (F H m a c N : PTm n) : PTm n := stage F H m a c (succ N)
def originalValue (H x y : PTm n) : PTm n := RationalBivariateGaussianEmbedding.bivariate H (length H) x y
@[simp] theorem subst_input {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    (input F H m a c N).subst σ = input (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_remainder {k : ℕ} (σ : Fin n → PTm k) (F H m a c N : PTm n) :
    Syn.subst σ (remainder F H m a c N) = remainder (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by simp [remainder]
@[simp] theorem subst_originalValue {k : ℕ} (σ : Fin n → PTm k) (H x y : PTm n) :
    Syn.subst σ (originalValue H x y) = originalValue (Syn.subst σ H) (Syn.subst σ x) (Syn.subst σ y) := by simp [originalValue]

theorem remainder_shape (F H m a c N : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) : Γ ⊢[PRAAx]
    rowShape (remainder F H m a c N) m (width a c (succ N)) :=
  stage_shape _ _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))) (le_refl _)

theorem remainder_rows_embedded (F H m a c N : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) : Γ ⊢[PRAAx]
    rowsEmbedded (remainder F H m a c N) (targetStage F H m a c (succ N) (succ N)) m (width a c (succ N)) :=
  stage_rows_embedded _ _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))) (le_refl _)

theorem remainder_coefficient (F H m a c N r s : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (width a c (succ N))) : Γ ⊢[PRAAx]
    embed (entry (entry (remainder F H m a c N) r) s) ≐ entry (entry (targetStage F H m a c (succ N) (succ N)) r) s :=
  RationalPolynomialMonicCompanionGaussianEmbedding.embedded_at _ _ _ _
    (row_embedded_at _ _ _ _ _ (remainder_rows_embedded _ _ _ _ _ _ h) hr) ((succ_monus_succ _ _).eqTrans hs)

theorem reduction_evaluation (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic F m x y) scalarZero) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (remainder F H m a c N) m x y ≐
      RationalBivariateGaussianEmbedding.bivariate H (succ N) x y := by
  have hm := Prf.andE₁ h
  have hF := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hH := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have curve := (RationalBivariateGaussianEmbedding.monic_zero_iff F m c x y hF).iffMp hCurve
  have first := RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (remainder F H m a c N) (targetStage F H m a c (succ N) (succ N)) m (width a c (succ N)) x y
    (remainder_shape _ _ _ _ _ _ h) (GaussianPolynomialMonicHornerReduction.stage_shape _ _ _ _ _ _)
    (remainder_rows_embedded _ _ _ _ _ _ h)
  have reduce := GaussianPolynomialMonicHornerReduction.prefix_evaluation
    (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix H (succ N) (succ a))
    m a c (succ N) (embed x) (embed y) (succ N) hm
    (RationalBivariateGaussianEmbedding.embedded_row_shape F m c)
    (RationalBivariateGaussianEmbedding.embedded_row_shape H (succ N) a) curve (le_refl _)
  have e := first.eqTrans (reduce.eqTrans
    ((congrAp3 GaussianRationalHorner.hornerF (GaussianPolynomialMonicCompanion.values_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
      (RationalBivariateGaussianEmbedding.bivariate_conjugacy H (succ N) a x y hH).eqSymm))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) e

theorem bivariate_count_congr (P R S x y : PTm n) (hR : Γ ⊢[PRAAx] R ≐ S) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate P R x y ≐ RationalBivariateGaussianEmbedding.bivariate P S x y := by
  ipra_congr (RationalBivariateGaussianEmbedding.bivariate (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [.eqRefl P, hR, .eqRefl x, .eqRefl y]

theorem original_evaluation (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic F m x y) scalarZero) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (remainder F H m a c N) m x y ≐ originalValue H x y := by
  have hLen : Γ ⊢[PRAAx] length H ≐ succ N := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact (reduction_evaluation _ _ _ _ _ _ _ _ h hCurve).eqTrans
    (bivariate_count_congr _ _ _ _ _ hLen.eqSymm)

theorem original_zero_iff (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic F m x y) scalarZero) : Γ ⊢[PRAAx]
    Fm.iff (RationalArgmin.rationalEq (originalValue H x y) scalarZero)
      (RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.bivariate (remainder F H m a c N) m x y) scalarZero) := by
  have e := embed_congr (original_evaluation F H m a c N x y h hCurve)
  exact .andI
    (.impI ((RationalGaussianEmbedding.zero_iff _).iffMp
      (e.wk.eqTrans ((RationalGaussianEmbedding.zero_iff _).iffMpr Prf.hyp0))))
    (.impI ((RationalGaussianEmbedding.zero_iff _).iffMp
      (e.wk.eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff _).iffMpr Prf.hyp0))))

theorem remainder_length (F H m a c N : PTm n) : Γ ⊢[PRAAx] length (remainder F H m a c N) ≐ m := stage_length _ _ _ _ _ _
theorem remainder_computed_shape (F H m a c N : PTm n) : Γ ⊢[PRAAx]
    rowShape (remainder F H m a c N) m (width a c (succ N)) := stage_computed_shape _ _ _ _ _ _
theorem remainder_coefficient_well_formed (F H m a c N r s : PTm n)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (width a c (succ N))) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (remainder F H m a c N) r) s) := by
  have e := (entry_congr (entry_congr (stage_succ F H m a c N) (.eqRefl r)) (.eqRefl s)).eqTrans
    (RationalPolynomialConstantInjectionGaussianEmbedding.coefficient_lookup _ _ _ _ _ _ _ hr hs)
  exact RationalArithmetic.guard_congr e (RationalArithmetic.add_guard _ _)

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
theorem returned_length (F H m a c N : PTm n) : Γ ⊢[PRAAx] length (run F H m a c N) ≐ m :=
  (congrFst (program_at _ _ _ _ _ _)).eqTrans (remainder_length _ _ _ _ _ _)
theorem returned_shape (F H m a c N : PTm n) : Γ ⊢[PRAAx] rowShape (run F H m a c N) m (width a c (succ N)) :=
  row_shape_congr (program_at _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (remainder_computed_shape _ _ _ _ _ _)
theorem returned_coefficient (F H m a c N r s : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (width a c (succ N))) : Γ ⊢[PRAAx]
    embed (entry (entry (run F H m a c N) r) s) ≐ entry (entry (targetStage F H m a c (succ N) (succ N)) r) s :=
  (embed_congr (entry_congr (entry_congr (program_at _ _ _ _ _ _) (.eqRefl _)) (.eqRefl _))).eqTrans
    (remainder_coefficient _ _ _ _ _ _ _ _ h hr hs)

theorem bivariate_code_congr (P Q R x y : PTm n) (hP : Γ ⊢[PRAAx] P ≐ Q) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate P R x y ≐ RationalBivariateGaussianEmbedding.bivariate Q R x y := by
  ipra_congr (RationalBivariateGaussianEmbedding.bivariate (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [hP, .eqRefl R, .eqRefl x, .eqRefl y]
theorem returned_evaluation (F H m a c N x y : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hCurve : Γ ⊢[PRAAx] RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic F m x y) scalarZero) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (run F H m a c N) m x y ≐ originalValue H x y :=
  (bivariate_code_congr _ _ _ _ _ (program_at _ _ _ _ _ _)).eqTrans (original_evaluation _ _ _ _ _ _ _ _ h hCurve)

theorem actual_rational_remainder_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stage (var 0) (var 1) (var 2) (var 3) (var 4) zero ≐ zeroRows (var 2) (var 3) ⋏
      stage (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) ≐
        advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.andI (stage_zero _ _ _ _ _) (stage_succ _ _ _ _ _ _))
theorem actual_rational_remainder_computed_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ var 2 ⋏
      rowShape (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (width (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.andI (stage_length _ _ _ _ _ _) (stage_computed_shape _ _ _ _ _ _))
theorem actual_rational_remainder_prefix_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 5) (var 3) ⟶ le (var 6) (var 5) ⟶
      pairedRows (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (targetStage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 2) (width (var 3) (var 4) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (stage_profile _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_remainder_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ lt (var 6) (var 2) ⟶ le (var 7) (width (var 3) (var 4) (succ (var 5))) ⟶
      embed (entry (entry (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7)) ≐
        entry (entry (targetStage (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (succ (var 5))) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (remainder_coefficient _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_remainder_canonical_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (lt (var 6) (var 2) ⟶ le (var 7) (width (var 3) (var 4) (succ (var 5))) ⟶
      RationalNormalForm.wellFormed (entry (entry (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (.impI (remainder_coefficient_well_formed _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_remainder_original_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic (var 0) (var 2) (var 6) (var 7)) scalarZero ⟶
        RationalBivariateGaussianEmbedding.bivariate (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6) (var 7) ≐
          originalValue (var 1) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (original_evaluation _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_remainder_original_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic (var 0) (var 2) (var 6) (var 7)) scalarZero ⟶
        Fm.iff (RationalArgmin.rationalEq (originalValue (var 1) (var 6) (var 7)) scalarZero)
          (RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.bivariate
            (remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6) (var 7)) scalarZero)) :=
  closeUniv 8 (.impI (.impI (original_zero_iff _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_remainder_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ remainder (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_rational_remainder_returned_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ var 2 ⋏
      rowShape (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (width (var 3) (var 4) (succ (var 5)))) :=
  closeUniv 6 (.andI (returned_length _ _ _ _ _ _) (returned_shape _ _ _ _ _ _))
theorem actual_rational_remainder_returned_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic (var 0) (var 2) (var 6) (var 7)) scalarZero ⟶
        RationalBivariateGaussianEmbedding.bivariate (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (var 6) (var 7) ≐
          originalValue (var 1) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (returned_evaluation _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPolynomialMonicHornerReductionGaussianEmbedding
