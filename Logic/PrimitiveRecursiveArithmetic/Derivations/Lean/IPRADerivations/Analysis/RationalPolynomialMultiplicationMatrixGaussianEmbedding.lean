import IPRADerivations.Analysis.RationalPolynomialMonicCompanionGaussianEmbedding
import IPRADerivations.Analysis.GaussianPolynomialMultiplicationMatrix
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original rational polynomial multiplication matrix

The actual rational companion is iterated with numerical X-width a+j*c.
A compiled bounded QF invariant derives row shapes and every coefficient
embedding. The stored matrix reverses descending Y rows explicitly and
pads each actual column to the original common numerical width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialMultiplicationMatrixGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialMonicCompanionGaussianEmbedding
  (normalizedRow normalized_length rowsEmbedded original_rows_embedded companion companion_length companion_row_shape)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open GaussianPolynomialMultiplicationMatrix (bound_zero bound_succ slot padding slot_range stage_bound data packedBody packed_body_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def bound (a c j : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.bound a c j
def width (m a c : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.width m a c
@[simp] theorem subst_bound {l : ℕ} (σ : Fin n → PTm l) (a c j : PTm n) :
    Syn.subst σ (bound a c j) = bound (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [bound]
@[simp] theorem subst_width {l : ℕ} (σ : Fin n → PTm l) (m a c : PTm n) :
    Syn.subst σ (width m a c) = width (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [width]

def normalizeBody : PTm 2 := normalizedRow (entry (var 1) (var 0))
def normalizedRows (G m : PTm n) : PTm n := sequence normalizeBody m G
def advance (F m a c j H : PTm n) : PTm n := companion F H m (bound a c j) c
def advanceF : PR 6 := PTm.toPR (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def initial : PTm 1 := normalizedRows (fstT (sndT (var 0))) (fstT (sndT (sndT (var 0))))
def stepBody : PTm 3 := PTm.app advanceF ![fstT (var 2),fstT (sndT (sndT (var 2))),
  fstT (sndT (sndT (sndT (var 2)))),sndT (sndT (sndT (sndT (var 2)))),var 0,var 1]
def stageF : PR 2 := rec2 initial stepBody
def stage (F G m a c j : PTm n) : PTm n := ap2 stageF j (data F G m a c)
def targetStage (F G m a c j : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.stage
  (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c j
@[simp] theorem subst_normalizedRows {l : ℕ} (σ : Fin n → PTm l) (G m : PTm n) :
    Syn.subst σ (normalizedRows G m) = normalizedRows (Syn.subst σ G) (Syn.subst σ m) := by simp [normalizedRows]
@[simp] theorem subst_advance {l : ℕ} (σ : Fin n → PTm l) (F m a c j H : PTm n) :
    Syn.subst σ (advance F m a c j H) = advance (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) (Syn.subst σ H) := by simp [advance]
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (F G m a c j : PTm n) :
    Syn.subst σ (stage F G m a c j) = stage (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [stage]
@[simp] theorem subst_targetStage {l : ℕ} (σ : Fin n → PTm l) (F G m a c j : PTm n) :
    Syn.subst σ (targetStage F G m a c j) = targetStage (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [targetStage]

theorem normalized_rows_length (G m : PTm n) : Γ ⊢[PRAAx] length (normalizedRows G m) ≐ m := sequence_length _ _ _
theorem normalized_rows_lookup (G m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (normalizedRows G m) r ≐ normalizedRow (entry G r) := by
  simpa only [normalizedRows,normalizeBody,inst2,RationalPolynomialMonicCompanionGaussianEmbedding.subst_normalizedRow,
    Foundations.MasterCertificate.subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using sequence_decode normalizeBody (x := G) hr
theorem normalized_rows_congr {G G' m m' : PTm n} (hG : Γ ⊢[PRAAx] G ≐ G') (hm : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx]
    normalizedRows G m ≐ normalizedRows G' m' := by
  ipra_congr (normalizedRows (var 0) (var 1) : PTm 2) with [hG, hm]
theorem advance_program (F m a c j H : PTm n) : Γ ⊢[PRAAx] PTm.app advanceF ![F,m,a,c,j,H] ≐ advance F m a c j H := by
  simpa [advanceF] using toPR_eq (Γ := Γ) (advance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,m,a,c,j,H]
theorem stage_zero (F G m a c : PTm n) : Γ ⊢[PRAAx] stage F G m a c zero ≐ normalizedRows G m := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data F G m a c)
  simp only [initial,subst_normalizedRows,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero] at e
  have tail := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have rest := (congrSnd tail).eqTrans (snd_pair G (pairT m (pairT a c)))
  exact e.eqTrans (normalized_rows_congr ((congrFst tail).eqTrans (fst_pair _ _)) ((congrFst rest).eqTrans (fst_pair _ _)))
theorem stage_succ (F G m a c j : PTm n) : Γ ⊢[PRAAx] stage F G m a c (succ j) ≐ companion F (stage F G m a c j) m (bound a c j) c := by
  have e := rec2_succ (Γ := Γ) initial stepBody j (data F G m a c)
  have vector : (fun i => Syn.subst ![j,stage F G m a c j,data F G m a c]
      ((![fstT (var 2),fstT (sndT (sndT (var 2))),fstT (sndT (sndT (sndT (var 2)))),
        sndT (sndT (sndT (sndT (var 2)))),var 0,var 1] : Fin 6 → PTm 3) i)) =
      ![fstT (data F G m a c),fstT (sndT (sndT (data F G m a c))),fstT (sndT (sndT (sndT (data F G m a c)))),
        sndT (sndT (sndT (sndT (data F G m a c)))),j,stage F G m a c j] := by funext i; fin_cases i <;> simp
  change Γ ⊢[PRAAx] stage F G m a c (succ j) ≐ PTm.app advanceF
    (fun i => Syn.subst ![j,stage F G m a c j,data F G m a c]
      ((![fstT (var 2),fstT (sndT (sndT (var 2))),fstT (sndT (sndT (sndT (var 2)))),
        sndT (sndT (sndT (sndT (var 2)))),var 0,var 1] : Fin 6 → PTm 3) i)) at e
  rw [vector] at e
  have tail := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have rest := (congrSnd tail).eqTrans (snd_pair G (pairT m (pairT a c)))
  have last := (congrSnd rest).eqTrans (snd_pair m (pairT a c))
  have fields := congrApp (Γ := Γ) advanceF
    (ts := ![fstT (data F G m a c),fstT (sndT (sndT (data F G m a c))),fstT (sndT (sndT (sndT (data F G m a c)))),
      sndT (sndT (sndT (sndT (data F G m a c)))),j,stage F G m a c j]) (us := ![F,m,a,c,j,stage F G m a c j])
    (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst rest).eqTrans (fst_pair _ _)
      · exact (congrFst last).eqTrans (fst_pair _ _)
      · exact (congrSnd last).eqTrans (snd_pair _ _)
      · exact .eqRefl _
      · exact .eqRefl _)
  exact e.eqTrans (fields.eqTrans (advance_program _ _ _ _ _ _))

def pairedRows (H K m b : PTm n) : Fm PTm n := rowShape H m b ⋏ rowsEmbedded H K m b
def profile (F G m a c j : PTm n) : Fm PTm n := pairedRows (stage F G m a c j) (targetStage F G m a c j) m (bound a c j)
@[simp] theorem subst_pairedRows {l : ℕ} (σ : Fin n → PTm l) (H K m b : PTm n) :
    (pairedRows H K m b).subst σ = pairedRows (Syn.subst σ H) (Syn.subst σ K) (Syn.subst σ m) (Syn.subst σ b) := by simp [pairedRows]
@[simp] theorem subst_profile {l : ℕ} (σ : Fin n → PTm l) (F G m a c j : PTm n) :
    (profile F G m a c j).subst σ = profile (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ j) := by simp [profile]
theorem paired_rows_congr {H H' K K' m b b' : PTm n} (hH : Γ ⊢[PRAAx] H ≐ H') (hK : Γ ⊢[PRAAx] K ≐ K')
    (hb : Γ ⊢[PRAAx] b ≐ b') (h : Γ ⊢[PRAAx] pairedRows H K m b) : Γ ⊢[PRAAx] pairedRows H' K' m b' := by
  have out := Prf.eqSubst (Γ := Γ) (pairedRows (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![H,K,m,b] ![H',K',m,b'] (fun i => by fin_cases i; exact hH; exact hK; exact .eqRefl _; exact hb) (by simpa using h)
  simpa using out
theorem normalized_profile (G m a : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    pairedRows (normalizedRows G m) (GaussianPolynomialMultiplicationMatrix.normalizedRows (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m) m a := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hG.shift
  refine .andI (.allI (.impI ?_)) (.allI (.impI ?_))
  · simpa only [Syn.shift,subst_normalizedRows,ConciseIPRA.PTm.subst_succ,length] using
      (congrFst (normalized_rows_lookup (Syn.shift G) (Syn.shift m) (var 0) Prf.hyp0)).eqTrans
        ((normalized_length _).eqTrans (row_shape_at _ _ _ _ gs.wk Prf.hyp0))
  · let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have value := RationalPolynomialMonicCompanionGaussianEmbedding.normalized_entries
      (entry (Syn.shift G) (var 0)) (entry (RationalRowSpanGaussianEmbedding.matrix (Syn.shift G) (Syn.shift m) (succ (Syn.shift a))) (var 0))
      (succ (Syn.shift a)) (row_shape_at _ _ _ _ gs.wk (Γ := Δ) Prf.hyp0)
      (RationalBivariateGaussianEmbedding.embedded_row_length _ _ _ _ Prf.hyp0)
      (RationalBivariateGaussianEmbedding.row_embedding _ _ _ _ Prf.hyp0)
    have moved := RationalPolynomialMonicCompanionGaussianEmbedding.embedded_congr
      (normalized_rows_lookup (Syn.shift G) (Syn.shift m) (var 0) (Γ := Δ) Prf.hyp0).eqSymm
      (GaussianPolynomialMultiplicationMatrix.normalized_rows_lookup _ _ _ Prf.hyp0).eqSymm value
    simpa only [Δ,Syn.shift,subst_normalizedRows,GaussianPolynomialMultiplicationMatrix.subst_normalizedRows,
      RationalRowSpanGaussianEmbedding.subst_matrix,ConciseIPRA.PTm.subst_succ] using moved

theorem profile_base (F G m a c : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx] profile F G m a c zero :=
  paired_rows_congr (stage_zero F G m a c).eqSymm (GaussianPolynomialMultiplicationMatrix.stage_zero _ _ _ _ _).eqSymm
    (bound_zero a c).eqSymm (normalized_profile G m a hG)
theorem profile_step (F G m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (ih : Γ ⊢[PRAAx] profile F G m a c j) : Γ ⊢[PRAAx] profile F G m a c (succ j) := by
  have hI : Γ ⊢[PRAAx] RationalPolynomialMonicCompanionGaussianEmbedding.transportInput
      F (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (stage F G m a c j) (targetStage F G m a c j) m (bound a c j) c :=
    .andI hm (.andI hF (.andI (RationalBivariateGaussianEmbedding.embedded_row_shape F m c)
      (.andI (.andE₁ ih) (.andI (GaussianPolynomialMultiplicationMatrix.stage_shape _ _ _ _ _ _ (RationalBivariateGaussianEmbedding.embedded_row_shape G m a))
        (.andI (original_rows_embedded F m c) (.andE₂ ih))))))
  exact paired_rows_congr (stage_succ F G m a c j).eqSymm (GaussianPolynomialMultiplicationMatrix.stage_succ _ _ _ _ _ _).eqSymm
    (bound_succ a c j).eqSymm (.andI (companion_row_shape _ _ _ _ _)
      (RationalPolynomialMonicCompanionGaussianEmbedding.companion_rows_embedded _ _ _ _ _ _ _ hI))

def rowShapeSyntax (H m b : PTm n) : BFm n := .all m (.eq (length (entry (Syn.shift H) (var 0))) (succ (Syn.shift b)))
def rowsEmbeddedSyntax (H K m b : PTm n) : BFm n := .all m
  (RationalPolynomialDeterminantTermsGaussianEmbedding.embeddedSyntax (entry (Syn.shift H) (var 0)) (entry (Syn.shift K) (var 0)) (succ (Syn.shift b)))
def profileSyntax (F G m a c j : PTm n) : BFm n := .and
  (rowShapeSyntax (stage F G m a c j) m (bound a c j)) (rowsEmbeddedSyntax (stage F G m a c j) (targetStage F G m a c j) m (bound a c j))
theorem profile_formula (F G m a c j : PTm n) : formula (profileSyntax F G m a c j) = profile F G m a c j := rfl
theorem stage_profile (F G m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx] profile F G m a c j := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hF.shift
  let S := profileSyntax (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)
  have all : Γ ⊢[PRAAx] .all (profile (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact profile_base F G m a c hG
    · simp only [S,profile_formula,subst_profile,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact profile_step _ _ _ _ _ _ ms.wk fs.wk Prf.hyp0
  simpa only [subst_profile,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem stage_shape (F G m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    rowShape (stage F G m a c j) m (bound a c j) := .andE₁ (stage_profile F G m a c j hm hF hG)
theorem stage_rows_embedded (F G m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    rowsEmbedded (stage F G m a c j) (targetStage F G m a c j) m (bound a c j) := .andE₂ (stage_profile F G m a c j hm hF hG)
def matrixEntry (F G m a c r j : PTm n) : PTm n := RationalPolynomialBuffersGaussianEmbedding.leftPad
  (entry (stage F G m a c j) (slot m r)) (padding m a c j)
@[simp] theorem subst_matrixEntry {l : ℕ} (σ : Fin n → PTm l) (F G m a c r j : PTm n) :
    Syn.subst σ (matrixEntry F G m a c r j) = matrixEntry (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ r) (Syn.subst σ j) := by simp [matrixEntry]
theorem padding_width (m a c j : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    padding m a c j+succ (bound a c j) ≐ succ (width m a c) :=
  (by ipra_ring : Γ ⊢[PRAAx] padding m a c j+succ (bound a c j) ≐ succ (padding m a c j+bound a c j)).eqTrans
    (congrSucc ((add_comm _ _).eqTrans (eq_add_of_le (stage_bound m a c j hm hj)).eqSymm))
theorem matrix_entry_length (F G m a c r j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] length (matrixEntry F G m a c r j) ≐ succ (width m a c) :=
  (RationalPolynomialBuffersGaussianEmbedding.pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) (row_shape_at _ _ _ _ (stage_shape F G m a c j hm hF hG) (slot_range m r hr))).eqTrans (padding_width m a c j hm hj))
theorem matrix_entry_transport (F G m a c r j s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    embed (entry (matrixEntry F G m a c r j) s) ≐ entry (GaussianPolynomialMultiplicationMatrix.matrixEntry
      (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c r j) s :=
  RationalPolynomialMonicCompanionGaussianEmbedding.pad_transport _ _ (succ (bound a c j)) (padding m a c j) s
    (row_shape_at _ _ _ _ (stage_shape F G m a c j hm hF hG) (slot_range m r hr))
    (row_shape_at _ _ _ _ (GaussianPolynomialMultiplicationMatrix.stage_shape _ _ _ _ _ _
      (RationalBivariateGaussianEmbedding.embedded_row_shape G m a)) (slot_range m r hr))
    (RationalPolynomialMonicCompanionGaussianEmbedding.row_embedded_at _ _ _ _ _ (stage_rows_embedded F G m a c j hm hF hG) (slot_range m r hr))
    (lt_congr (.eqRefl _) (padding_width m a c j hm hj).eqSymm ((succ_monus_succ _ _).eqTrans hs))

def columnProgram : PR 6 := PTm.toPR (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def columns (F G m a c : PTm n) : PTm n := sequence (packedBody columnProgram) m (data F G m a c)
def entryProgram : PR 7 := PTm.toPR (matrixEntry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def entryBody : PTm 3 := PTm.app entryProgram ![fstT (var 2),fstT (sndT (var 2)),fstT (sndT (sndT (var 2))),
  fstT (sndT (sndT (sndT (var 2)))),sndT (sndT (sndT (sndT (var 2)))),var 0,var 1]
def matrix (F G m a c : PTm n) : PTm n := GaussianRationalFiberVandermonde.table entryBody m m (data F G m a c)
@[simp] theorem subst_columns {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (columns F G m a c) = columns (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [columns]
@[simp] theorem subst_matrix {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (matrix F G m a c) = matrix (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [matrix]
theorem columns_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (columns F G m a c) ≐ m := sequence_length _ _ _
theorem column_program_at (F G m a c j : PTm n) : Γ ⊢[PRAAx] PTm.app columnProgram ![F,G,m,a,c,j] ≐ stage F G m a c j := by
  simpa [columnProgram] using toPR_eq (Γ := Γ) (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,G,m,a,c,j]
theorem columns_lookup (F G m a c j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    entry (columns F G m a c) j ≐ stage F G m a c j :=
  (sequence_decode (packedBody columnProgram) hj).eqTrans ((packed_body_at _ _ _ _ _ _ _).eqTrans (column_program_at _ _ _ _ _ _))
theorem entry_program_at (F G m a c r j : PTm n) : Γ ⊢[PRAAx] PTm.app entryProgram ![F,G,m,a,c,r,j] ≐ matrixEntry F G m a c r j := by
  simpa [entryProgram] using toPR_eq (Γ := Γ) (matrixEntry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![F,G,m,a,c,r,j]
theorem entry_body_at (F G m a c r j : PTm n) : Γ ⊢[PRAAx] Syn.subst ![r,j,data F G m a c] entryBody ≐ matrixEntry F G m a c r j := by
  simp only [entryBody,ConciseIPRA.PTm.subst_app]
  have vector : (fun i => Syn.subst ![r,j,data F G m a c]
      ((![fstT (var 2),fstT (sndT (var 2)),fstT (sndT (sndT (var 2))),fstT (sndT (sndT (sndT (var 2)))),
        sndT (sndT (sndT (sndT (var 2)))),var 0,var 1] : Fin 7 → PTm 3) i)) =
      ![fstT (data F G m a c),fstT (sndT (data F G m a c)),fstT (sndT (sndT (data F G m a c))),
        fstT (sndT (sndT (sndT (data F G m a c)))),sndT (sndT (sndT (sndT (data F G m a c)))),r,j] := by funext i; fin_cases i <;> simp
  rw [vector]
  have e := snd_pair (Γ := Γ) F (pairT G (pairT m (pairT a c)))
  have f := (congrSnd e).eqTrans (snd_pair G (pairT m (pairT a c)))
  have g := (congrSnd f).eqTrans (snd_pair m (pairT a c))
  have h := congrApp (Γ := Γ) entryProgram
    (ts := ![fstT (data F G m a c),fstT (sndT (data F G m a c)),fstT (sndT (sndT (data F G m a c))),
      fstT (sndT (sndT (sndT (data F G m a c)))),sndT (sndT (sndT (sndT (data F G m a c)))),r,j]) (us := ![F,G,m,a,c,r,j])
    (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst e).eqTrans (fst_pair _ _)
      · exact (congrFst f).eqTrans (fst_pair _ _)
      · exact (congrFst g).eqTrans (fst_pair _ _)
      · exact (congrSnd g).eqTrans (snd_pair _ _)
      · exact .eqRefl _
      · exact .eqRefl _)
  exact h.eqTrans (entry_program_at F G m a c r j)
theorem matrix_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (matrix F G m a c) ≐ m := GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem matrix_cell (F G m a c r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.cell (matrix F G m a c) r j ≐ matrixEntry F G m a c r j :=
  (GaussianRationalFiberVandermonde.table_lookup _ _ _ _ _ _ hr hj).eqTrans (entry_body_at F G m a c r j)
theorem target_matrix_cell (F G m a c r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.cell (GaussianPolynomialMultiplicationMatrix.matrix F G m a c) r j ≐
      GaussianPolynomialMultiplicationMatrix.matrixEntry F G m a c r j :=
  (entry_congr (GaussianPolynomialMultiplicationMatrix.matrix_lookup _ _ _ _ _ _ hr) (.eqRefl j)).eqTrans
    (GaussianPolynomialMultiplicationMatrix.matrix_row_lookup _ _ _ _ _ _ _ hj)
theorem matrix_entry_embedding (F G m a c r j s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    embed (entry (GaussianPolynomialDeterminantTerms.cell (matrix F G m a c) r j) s) ≐ entry (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
        (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c) r j) s :=
  (embed_congr (entry_congr (matrix_cell F G m a c r j hr hj) (.eqRefl s))).eqTrans
    ((matrix_entry_transport F G m a c r j s hm hF hG hr hj hs).eqTrans
      (entry_congr (target_matrix_cell _ _ _ _ _ _ _ hr hj).eqSymm (.eqRefl s)))

def input (F G m a c : PTm n) : Fm PTm n := le one m ⋏ (rowShape F m c ⋏ rowShape G m a)
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    (input F G m a c).subst σ = input (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [input]
theorem matrix_row_length (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (matrix F G m a c) r) ≐ m := GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ hr
theorem matrix_polynomial_length (F G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input F G m a c)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (GaussianPolynomialDeterminantTerms.cell (matrix F G m a c) r j) ≐ succ (width m a c) :=
  (congrFst (matrix_cell F G m a c r j hr hj)).eqTrans
    (matrix_entry_length F G m a c r j (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hr hj)
theorem matrix_row_cells (F G m a c r : PTm n) (h : Γ ⊢[PRAAx] input F G m a c) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.rowCells (matrix F G m a c) m (width m a c) r := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_matrix,subst_width,ConciseIPRA.PTm.subst_succ] using
    matrix_polynomial_length (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift r) (var 0) ss.wk rs.wk Prf.hyp0
theorem matrix_shape (F G m a c : PTm n) (h : Γ ⊢[PRAAx] input F G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.tableShape (matrix F G m a c) m (width m a c) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  refine .andI (matrix_length _ _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_matrix] using
      matrix_row_length (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) Prf.hyp0
  · simpa only [Syn.shift,subst_matrix,subst_width] using
      matrix_row_cells (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) ss.wk Prf.hyp0

def matrixF : PR 5 := PTm.toPR (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
def columnsF : PR 5 := PTm.toPR (columns (var 0) (var 1) (var 2) (var 3) (var 4))
def output (F G m a c : PTm n) : PTm n := pairT (columns F G m a c) (matrix F G m a c)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := PTm.app outputF ![F,G,m,a,c]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (output F G m a c) = output (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (run F G m a c) = run (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem matrix_program (F G m a c : PTm n) : Γ ⊢[PRAAx] PTm.app matrixF ![F,G,m,a,c] ≐ matrix F G m a c := by
  simpa only [matrixF,subst_matrix,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (matrix (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem columns_program (F G m a c : PTm n) : Γ ⊢[PRAAx] PTm.app columnsF ![F,G,m,a,c] ≐ columns F G m a c := by
  simpa only [columnsF,subst_columns,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (columns (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ output F G m a c := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_columns (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (run F G m a c) ≐ columns F G m a c :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_matrix (F G m a c : PTm n) : Γ ⊢[PRAAx] sndT (run F G m a c) ≐ matrix F G m a c :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_entry_embedding (F G m a c r j s : PTm n) (h : Γ ⊢[PRAAx] input F G m a c)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hs : Γ ⊢[PRAAx] le s (width m a c)) : Γ ⊢[PRAAx]
    embed (entry (GaussianPolynomialDeterminantTerms.cell (sndT (run F G m a c)) r j) s) ≐ entry (GaussianPolynomialDeterminantTerms.cell
      (GaussianPolynomialMultiplicationMatrix.matrix (RationalRowSpanGaussianEmbedding.matrix F m (succ c))
        (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c) r j) s :=
  (embed_congr (entry_congr (entry_congr (entry_congr (returned_matrix F G m a c) (.eqRefl r)) (.eqRefl j)) (.eqRefl s))).eqTrans
    (matrix_entry_embedding F G m a c r j s (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hr hj hs)

theorem actual_rational_matrix_column_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stage (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) ≐ companion (var 0)
      (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (bound (var 3) (var 4) (var 5)) (var 4)) :=
  closeUniv 6 (stage_succ _ _ _ _ _ _)
theorem actual_rational_matrix_profile_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ profile (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (stage_profile _ _ _ _ _ _ (.andE₁ Prf.hyp0) (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_rational_matrix_columns_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 2) ⟶ entry (columns (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
      stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (.impI (columns_lookup _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_matrix_orientation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶ GaussianPolynomialDeterminantTerms.cell
      (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6) ≐ RationalPolynomialBuffersGaussianEmbedding.leftPad
        (entry (stage (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) (slot (var 2) (var 5)))
          (padding (var 2) (var 3) (var 4) (var 6))) := closeUniv 7 (.impI (.impI (matrix_cell _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_matrix_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ GaussianPolynomialDeterminantTerms.tableShape
      (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (width (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (matrix_shape _ _ _ _ _ Prf.hyp0))
theorem actual_rational_matrix_polynomial_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶
      length (GaussianPolynomialDeterminantTerms.cell (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6)) ≐
        succ (width (var 2) (var 3) (var 4))) := closeUniv 7 (.impI (.impI (.impI (matrix_polynomial_length _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_multiplication_matrix_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶ lt (var 6) (var 2) ⟶
      le (var 7) (width (var 2) (var 3) (var 4)) ⟶ embed (entry (GaussianPolynomialDeterminantTerms.cell
        (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6)) (var 7)) ≐ entry (GaussianPolynomialDeterminantTerms.cell
          (GaussianPolynomialMultiplicationMatrix.matrix (RationalRowSpanGaussianEmbedding.matrix (var 0) (var 2) (succ (var 4)))
            (RationalRowSpanGaussianEmbedding.matrix (var 1) (var 2) (succ (var 3))) (var 2) (var 3) (var 4)) (var 5) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (matrix_entry_embedding _ _ _ _ _ _ _ _
    (.andE₁ Prf.hyp0.wk.wk.wk) (.andE₁ (.andE₂ Prf.hyp0.wk.wk.wk)) (.andE₂ (.andE₂ Prf.hyp0.wk.wk.wk)) Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_matrix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_rational_matrix_returned_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ columns (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
      sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ matrix (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.andI (returned_columns _ _ _ _ _) (returned_matrix _ _ _ _ _))

end LeanProofs.IPRA.Analysis.RationalPolynomialMultiplicationMatrixGaussianEmbedding
