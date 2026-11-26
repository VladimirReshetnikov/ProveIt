import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialConstantInjectionGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Translation.GaussianPolynomialYShift

/-!
# Original rational multiplication by the second indeterminate

Actual original rational coefficient rows are normalized, padded in X and
followed by a genuine polynomial-zero row. Original rectangular shape and
bounded coefficient embeddings derive storage, Gaussian transport and the
literal original bivariate multiply-by-Y law. No output law is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialYShiftGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialMonicCompanionGaussianEmbedding (normalizedRow normalized_length normalized_entries rowsEmbedded row_embedded_at)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open RationalPolynomialBuffersGaussianEmbedding (zeros zeros_length leftPad pad_length)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def row (G m a d r : PTm n) : PTm n :=
  sel (eqb r m) (zeros (succ (a+d))) (leftPad (normalizedRow (entry G r)) d)

def data (G m a d : PTm n) : PTm n := pairT G (pairT m (pairT a d))
def rowBody : PTm 2 := row (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def shiftY (G m a d : PTm n) : PTm n := sequence rowBody (succ m) (data G m a d)

@[simp] theorem subst_row {k : ℕ} (σ : Fin n → PTm k) (G m a d r : PTm n) :
    Syn.subst σ (row G m a d r) = row (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [row,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (G m a d : PTm n) :
    Syn.subst σ (data G m a d) = data (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [data]
@[simp] theorem subst_shiftY {k : ℕ} (σ : Fin n → PTm k) (G m a d : PTm n) :
    Syn.subst σ (shiftY G m a d) = shiftY (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [shiftY]

theorem row_body_at (G m a d r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (data G m a d) ≐ row G m a d r := by
  have tail := snd_pair (Γ := Γ) G (pairT m (pairT a d))
  have rest := (congrSnd tail).eqTrans (snd_pair m (pairT a d))
  simp only [rowBody,inst2,subst_row,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (row (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (data G m a d),fstT (sndT (data G m a d)),fstT (sndT (sndT (data G m a d))),
      sndT (sndT (sndT (data G m a d))),r])
    (σ' := ![G,m,a,d,r]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst rest).eqTrans (fst_pair _ _)
      · exact (congrSnd rest).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
theorem shift_length (G m a d : PTm n) : Γ ⊢[PRAAx] length (shiftY G m a d) ≐ succ m := sequence_length _ _ _
theorem shift_lookup (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx]
    entry (shiftY G m a d) r ≐ row G m a d r :=
  (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _ _)
theorem last_row (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] r ≐ m) : Γ ⊢[PRAAx] row G m a d r ≐ zeros (succ (a+d)) :=
  sel_one (eqb_of_eq hr)
theorem earlier_row (G m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] row G m a d r ≐ leftPad (normalizedRow (entry G r)) d :=
  sel_zero (eqb_of_ne (.impI (lt_irrefl _ _ (lt_congr (.eqRefl _) Prf.hyp0.eqSymm hr.wk))))
theorem padded_length (G m a d r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] length (leftPad (normalizedRow (entry G r)) d) ≐ succ (a+d) :=
  (pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hr))).eqTrans (by ipra_ring))

theorem shifted_row_length (G m a d r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx] length (entry (shiftY G m a d) r) ≐ succ (a+d) := by
  have eq := shift_lookup G m a d r hr
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hr)) ?_ ?_
  · exact (congrFst (eq.wk.eqTrans (earlier_row _ _ _ _ _ Prf.hyp0))).eqTrans (padded_length _ _ _ _ _ hG.wk Prf.hyp0)
  · exact (congrFst (eq.wk.eqTrans (last_row _ _ _ _ _ Prf.hyp0))).eqTrans (zeros_length _)

theorem shift_shape (G m a d : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    rowShape (shiftY G m a d) (succ m) (a+d) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_shiftY,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    shifted_row_length (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) gs.wk Prf.hyp0

theorem shift_entry_transport (G G' m a d r s : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) (hr : Γ ⊢[PRAAx] lt r (succ m))
    (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    embed (entry (entry (shiftY G m a d) r) s) ≐ entry (entry (GaussianPolynomialYShift.shiftY G' m a d) r) s := by
  have e := shift_lookup G m a d r hr
  have e' := GaussianPolynomialYShift.shift_lookup G' m a d r hr
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hr)) ?_ ?_
  · let Δ := lt r m :: Γ
    have hN := normalized_entries (entry G r) (entry G' r) (succ a)
      (row_shape_at _ _ _ _ hG.wk (Γ := Δ) Prf.hyp0) (row_shape_at _ _ _ _ hG'.wk Prf.hyp0)
      (row_embedded_at _ _ _ _ _ he.wk Prf.hyp0)
    have middle := RationalPolynomialMonicCompanionGaussianEmbedding.pad_transport
      (normalizedRow (entry G r)) (GaussianPolynomialMonicCompanion.normalizedRow (entry G' r)) (succ a) d s
      ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk (Γ := Δ) Prf.hyp0))
      ((GaussianPolynomialMonicCompanion.normalized_length _).eqTrans (row_shape_at _ _ _ _ hG'.wk Prf.hyp0)) hN
      (lt_congr (.eqRefl _) (by ipra_ring) ((succ_monus_succ _ _).eqTrans hs.wk))
    exact (embed_congr (entry_congr (e.wk.eqTrans (earlier_row _ _ _ _ _ Prf.hyp0)) (.eqRefl _))).eqTrans
      (middle.eqTrans (entry_congr (e'.wk.eqTrans (GaussianPolynomialYShift.earlier_row _ _ _ _ _ Prf.hyp0)) (.eqRefl _)).eqSymm)
  · exact (embed_congr (entry_congr (e.wk.eqTrans (last_row _ _ _ _ _ Prf.hyp0)) (.eqRefl _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans
        (entry_congr (e'.wk.eqTrans (GaussianPolynomialYShift.last_row _ _ _ _ _ Prf.hyp0)) (.eqRefl _)).eqSymm)

theorem shift_row_entries (G G' m a d r : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx]
    embeddedEntries (entry (shiftY G m a d) r) (entry (GaussianPolynomialYShift.shiftY G' m a d) r) (succ (a+d)) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have gs' : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG'.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using he.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (succ (Syn.shift m)) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift a+Syn.shift d)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift a+Syn.shift d) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift a+Syn.shift d)))
  simpa only [Δ,Syn.shift,subst_shiftY,GaussianPolynomialYShift.subst_shiftY,subst_entry,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    shift_entry_transport (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift r) (var 0)
      gs.wk gs'.wk es.wk rs.wk bound

theorem shift_rows_embedded (G G' m a d : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) : Γ ⊢[PRAAx]
    rowsEmbedded (shiftY G m a d) (GaussianPolynomialYShift.shiftY G' m a d) (succ m) (a+d) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have gs' : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG'.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_shiftY,GaussianPolynomialYShift.subst_shiftY,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    shift_row_entries (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) gs.wk gs'.wk es.wk Prf.hyp0

theorem shift_evaluation (G m a d x y : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (shiftY G m a d) (succ m) x y ≐
      RationalArithmetic.multiply y (RationalBivariateGaussianEmbedding.bivariate G m x y) := by
  let G' := RationalRowSpanGaussianEmbedding.matrix G m (succ a)
  have hG' : Γ ⊢[PRAAx] rowShape G' m a := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have he : Γ ⊢[PRAAx] rowsEmbedded G G' m a := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have e := (RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (shiftY G m a d) (GaussianPolynomialYShift.shiftY G' m a d) (succ m) (a+d) x y
    (shift_shape _ _ _ _ hG) (.andE₁ (.andE₂ (GaussianPolynomialYShift.shift_stored _ _ _ _ hG')))
    (shift_rows_embedded _ _ _ _ _ hG hG' he)).eqTrans
      ((GaussianPolynomialYShift.shift_evaluation G' m a d (embed x) (embed y)).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
          (RationalBivariateGaussianEmbedding.bivariate_conjugacy G m a x y hG).eqSymm).eqTrans
            (RationalGaussianEmbedding.embed_multiply _ _).eqSymm))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.multiply_guard _ _) e


def shiftF : PR 4 := PTm.toPR (shiftY (var 0) (var 1) (var 2) (var 3))
def run (G m a d : PTm n) : PTm n := PTm.app shiftF ![G,m,a,d]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (G m a d : PTm n) :
    Syn.subst σ (run G m a d) = run (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (G m a d : PTm n) : Γ ⊢[PRAAx] run G m a d ≐ shiftY G m a d := by
  simpa [run,shiftF] using toPR_eq (Γ := Γ) (shiftY (var 0) (var 1) (var 2) (var 3) : PTm 4) ![G,m,a,d]
theorem returned_length (G m a d : PTm n) : Γ ⊢[PRAAx] length (run G m a d) ≐ succ m :=
  (congrFst (program_at _ _ _ _)).eqTrans (shift_length _ _ _ _)

theorem actual_rational_y_shift_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowShape (var 0) (var 1) (var 2) ⟶
      (length (shiftY (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1) ⋏
        rowShape (shiftY (var 0) (var 1) (var 2) (var 3)) (succ (var 1)) (var 2+var 3))) :=
  closeUniv 4 (.impI (.andI (shift_length _ _ _ _) (shift_shape _ _ _ _ Prf.hyp0)))
theorem actual_rational_y_shift_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowShape (var 0) (var 2) (var 3) ⟶ rowShape (var 1) (var 2) (var 3) ⟶ rowsEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      lt (var 5) (succ (var 2)) ⟶ le (var 6) (var 3+var 4) ⟶
        embed (entry (entry (shiftY (var 0) (var 2) (var 3) (var 4)) (var 5)) (var 6)) ≐
          entry (entry (GaussianPolynomialYShift.shiftY (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (shift_entry_transport _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_rational_y_shift_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 1) (var 2) ⟶
      RationalBivariateGaussianEmbedding.bivariate (shiftY (var 0) (var 1) (var 2) (var 3)) (succ (var 1)) (var 4) (var 5) ≐
        RationalArithmetic.multiply (var 5) (RationalBivariateGaussianEmbedding.bivariate (var 0) (var 1) (var 4) (var 5))) :=
  closeUniv 6 (.impI (shift_evaluation _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_y_shift_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ shiftY (var 0) (var 1) (var 2) (var 3) ⋏
      length (run (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1)) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (returned_length _ _ _ _))

end LeanProofs.IPRA.Analysis.RationalPolynomialYShiftGaussianEmbedding
