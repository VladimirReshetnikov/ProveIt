import IPRADerivations.Analysis.Polynomials.Translation.RationalPolynomialYShiftGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePolynomialBuffers

/-!
# Actual original rational rectangular padding and addition

Every outer entry is an actual X-polynomial coefficient buffer. Outer
leading padding uses polynomial-zero rows; addition applies original
rational coefficient addition within each row. Bounded literal Gaussian
transport and the original all-query evaluation laws are derived.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBivariatePolynomialBuffersGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialMonicCompanionGaussianEmbedding (normalizedRow normalized_length normalized_entries rowsEmbedded row_embedded_at embedded_at)
open RationalPolynomialBuffersGaussianEmbedding (zeros zeros_length leftPad added added_length added_lookup embeddedEntries)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def padRow (G a dx dy r : PTm n) : PTm n :=
  sel (Signum.sg (monus dy r)) (zeros (succ (a+dx)))
    (leftPad (normalizedRow (entry G (monus r dy))) dx)
def padData (G a dx dy : PTm n) : PTm n := pairT G (pairT a (pairT dx dy))
def padBody : PTm 2 := padRow (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def pad (G m a dx dy : PTm n) : PTm n := sequence padBody (dy+m) (padData G a dx dy)
def addRow (A B a r : PTm n) : PTm n := added (entry A r) (entry B r) (succ a)
def addData (A B a : PTm n) : PTm n := pairT A (pairT B a)
def addBody : PTm 2 := addRow (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def add (A B m a : PTm n) : PTm n := sequence addBody m (addData A B a)

ipra_subst padRow [sel, Signum.sg]
ipra_subst padData
ipra_subst pad
ipra_subst addRow
ipra_subst addData
ipra_subst add

theorem pad_row_before (G a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r dy) : Γ ⊢[PRAAx]
    padRow G a dx dy r ≐ zeros (succ (a+dx)) := sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem pad_row_after (G a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] le dy r) : Γ ⊢[PRAAx]
    padRow G a dx dy r ≐ leftPad (normalizedRow (entry G (monus r dy))) dx := sel_zero (AnalyticNumberTheory.Totatives.sg_le hr)
theorem pad_body_at (G a dx dy r : PTm n) : Γ ⊢[PRAAx] inst2 padBody r (padData G a dx dy) ≐ padRow G a dx dy r := by
  have tail := snd_pair (Γ := Γ) G (pairT a (pairT dx dy))
  have rest := (congrSnd tail).eqTrans (snd_pair a (pairT dx dy))
  simp only [padBody,inst2,subst_padRow,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (padRow (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (padData G a dx dy),fstT (sndT (padData G a dx dy)),fstT (sndT (sndT (padData G a dx dy))),
      sndT (sndT (sndT (padData G a dx dy))),r]) (σ' := ![G,a,dx,dy,r]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact tail.fstE
      · exact rest.fstE
      · exact rest.sndE
      · exact .eqRefl _)
theorem pad_length (G m a dx dy : PTm n) : Γ ⊢[PRAAx] length (pad G m a dx dy) ≐ dy+m := sequence_length _ _ _
theorem pad_lookup (G m a dx dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx]
    entry (pad G m a dx dy) r ≐ padRow G a dx dy r := (sequence_decode padBody hr).eqTrans (pad_body_at _ _ _ _ _)
theorem pad_tail_index (m dy r : PTm n) (hr : Γ ⊢[PRAAx] lt r (dy+m)) (hdy : Γ ⊢[PRAAx] le dy r) :
    Γ ⊢[PRAAx] lt (monus r dy) m := GaussianBivariatePolynomialBuffers.pad_tail_index m dy r hr hdy

theorem pad_row_length (G m a dx dy r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx] length (entry (pad G m a dx dy) r) ≐ succ (a+dx) := by
  have e := pad_lookup G m a dx dy r hr
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact (congrFst (e.wk.eqTrans (pad_row_before _ _ _ _ _ Prf.hyp0))).eqTrans (zeros_length _)
  · exact (congrFst (e.wk.eqTrans (pad_row_after _ _ _ _ _ Prf.hyp0))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.pad_length _ _).eqTrans
        ((congrAdd (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk (pad_tail_index _ _ _ hr.wk Prf.hyp0)))).eqTrans (by ipra_ring)))
theorem add_body_at (A B a r : PTm n) : Γ ⊢[PRAAx] inst2 addBody r (addData A B a) ≐ addRow A B a r := by
  simp only [addBody,inst2,subst_addRow,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) A (pairT B a)
  ipra_congr (addRow (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [(show _ ⊢[PRAAx] fstT (addData A B a) ≐ A from fst_pair _ _),
      (show _ ⊢[PRAAx] fstT (sndT (addData A B a)) ≐ B from tail.fstE),
      (show _ ⊢[PRAAx] sndT (sndT (addData A B a)) ≐ a from tail.sndE), .eqRefl r]
theorem add_length (A B m a : PTm n) : Γ ⊢[PRAAx] length (add A B m a) ≐ m := sequence_length _ _ _
theorem add_lookup (A B m a r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (add A B m a) r ≐ added (entry A r) (entry B r) (succ a) := (sequence_decode addBody hr).eqTrans (add_body_at _ _ _ _)
theorem add_coefficient (A B m a r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    entry (entry (add A B m a) r) s ≐ RationalArithmetic.add (entry (entry A r) s) (entry (entry B r) s) :=
  (entry_congr (add_lookup _ _ _ _ _ hr) (.eqRefl _)).eqTrans (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))
theorem pad_shape (G m a dx dy : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    rowShape (pad G m a dx dy) (dy+m) (a+dx) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pad,PTm.subst_add] using
    pad_row_length (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (var 0) gs.wk Prf.hyp0

theorem pad_entry_transport (G G' m a dx dy r s : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) (hr : Γ ⊢[PRAAx] lt r (dy+m))
    (hs : Γ ⊢[PRAAx] le s (a+dx)) : Γ ⊢[PRAAx]
    embed (entry (entry (pad G m a dx dy) r) s) ≐ entry (entry (GaussianBivariatePolynomialBuffers.pad G' m a dx dy) r) s := by
  have e := pad_lookup G m a dx dy r hr
  have e' := GaussianBivariatePolynomialBuffers.pad_lookup G' m a dx dy r hr
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact (embed_congr (entry_congr (e.wk.eqTrans (pad_row_before _ _ _ _ _ Prf.hyp0)) (.eqRefl _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans
        (entry_congr (e'.wk.eqTrans (GaussianBivariatePolynomialBuffers.pad_row_before _ _ _ _ _ Prf.hyp0)) (.eqRefl _)).eqSymm)
  · let Δ := le dy r :: Γ
    have index : Δ ⊢[PRAAx] lt (monus r dy) m := pad_tail_index m dy r hr.wk Prf.hyp0
    have hN := normalized_entries (entry G (monus r dy)) (entry G' (monus r dy)) (succ a)
      (row_shape_at _ _ _ _ hG.wk index) (row_shape_at _ _ _ _ hG'.wk index)
      (row_embedded_at _ _ _ _ _ he.wk index)
    have middle := RationalPolynomialMonicCompanionGaussianEmbedding.pad_transport
      (normalizedRow (entry G (monus r dy))) (GaussianPolynomialMonicCompanion.normalizedRow (entry G' (monus r dy))) (succ a) dx s
      ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk index))
      ((GaussianPolynomialMonicCompanion.normalized_length _).eqTrans (row_shape_at _ _ _ _ hG'.wk index)) hN
      (lt_congr (.eqRefl _) (by ipra_ring) ((succ_monus_succ _ _).eqTrans hs.wk))
    exact (embed_congr (entry_congr (e.wk.eqTrans (pad_row_after _ _ _ _ _ Prf.hyp0)) (.eqRefl _))).eqTrans
      (middle.eqTrans (entry_congr (e'.wk.eqTrans (GaussianBivariatePolynomialBuffers.pad_row_after _ _ _ _ _ Prf.hyp0)) (.eqRefl _)).eqSymm)

theorem pad_row_entries (G G' m a dx dy r : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) (hr : Γ ⊢[PRAAx] lt r (dy+m)) : Γ ⊢[PRAAx]
    embeddedEntries (entry (pad G m a dx dy) r) (entry (GaussianBivariatePolynomialBuffers.pad G' m a dx dy) r) (succ (a+dx)) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have gs' : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG'.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using he.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift dy+Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift a+Syn.shift dx)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift a+Syn.shift dx) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift a+Syn.shift dx)))
  simpa only [Δ,Syn.shift,subst_pad,GaussianBivariatePolynomialBuffers.subst_pad,subst_entry,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    pad_entry_transport (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (Syn.shift r) (var 0)
      gs.wk gs'.wk es.wk rs.wk bound

theorem pad_rows_embedded (G G' m a dx dy : PTm n)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) : Γ ⊢[PRAAx]
    rowsEmbedded (pad G m a dx dy) (GaussianBivariatePolynomialBuffers.pad G' m a dx dy) (dy+m) (a+dx) := by
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have gs' : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hG'.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pad,GaussianBivariatePolynomialBuffers.subst_pad,PTm.subst_add] using
    pad_row_entries (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift dx) (Syn.shift dy) (var 0) gs.wk gs'.wk es.wk Prf.hyp0

theorem add_shape (A B m a : PTm n) : Γ ⊢[PRAAx] rowShape (add A B m a) m a := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_add,length,ConciseIPRA.PTm.subst_succ] using
    (congrFst (add_lookup (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)).eqTrans (added_length _ _ _)

theorem add_entry_transport (A A' B B' m a r s : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' m a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    embed (entry (entry (add A B m a) r) s) ≐ entry (entry (GaussianBivariatePolynomialBuffers.add A' B' m a) r) s :=
  (embed_congr (add_coefficient _ _ _ _ _ _ hr hs)).eqTrans
    ((RationalGaussianEmbedding.embed_add _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr
        (embedded_at _ _ _ _ (row_embedded_at _ _ _ _ _ hA hr) ((succ_monus_succ _ _).eqTrans hs))
        (embedded_at _ _ _ _ (row_embedded_at _ _ _ _ _ hB hr) ((succ_monus_succ _ _).eqTrans hs))).eqTrans
          (GaussianBivariatePolynomialBuffers.add_coefficient _ _ _ _ _ _ hr hs).eqSymm))

theorem add_row_entries (A A' B B' m a r : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' m a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' m a)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    embeddedEntries (entry (add A B m a) r) (entry (GaussianBivariatePolynomialBuffers.add A' B' m a) r) (succ a) := by
  have as : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift A) (Syn.shift A') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift B) (Syn.shift B') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift a)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift a) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift a)))
  simpa only [Δ,Syn.shift,subst_add,GaussianBivariatePolynomialBuffers.subst_add,subst_entry,ConciseIPRA.PTm.subst_succ] using
    add_entry_transport (Syn.shift A) (Syn.shift A') (Syn.shift B) (Syn.shift B') (Syn.shift m) (Syn.shift a) (Syn.shift r) (var 0)
      as.wk bs.wk rs.wk bound

theorem add_rows_embedded (A A' B B' m a : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' m a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' m a) : Γ ⊢[PRAAx]
    rowsEmbedded (add A B m a) (GaussianBivariatePolynomialBuffers.add A' B' m a) m a := by
  have as : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift A) (Syn.shift A') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift B) (Syn.shift B') (Syn.shift m) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hB.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_add,GaussianBivariatePolynomialBuffers.subst_add] using
    add_row_entries (Syn.shift A) (Syn.shift A') (Syn.shift B) (Syn.shift B') (Syn.shift m) (Syn.shift a) (var 0) as.wk bs.wk Prf.hyp0


theorem pad_evaluation (G m a dx dy x y : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (pad G m a dx dy) (dy+m) x y ≐
      RationalBivariateGaussianEmbedding.bivariate G m x y := by
  let G' := RationalRowSpanGaussianEmbedding.matrix G m (succ a)
  have gs : Γ ⊢[PRAAx] rowShape G' m a := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have he : Γ ⊢[PRAAx] rowsEmbedded G G' m a := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have e := (RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (pad G m a dx dy) (GaussianBivariatePolynomialBuffers.pad G' m a dx dy) (dy+m) (a+dx) x y
    (pad_shape _ _ _ _ _ hG) (.andE₁ (.andE₂ (GaussianBivariatePolynomialBuffers.pad_stored _ _ _ _ _ gs)))
    (pad_rows_embedded _ _ _ _ _ _ hG gs he)).eqTrans
      ((GaussianBivariatePolynomialBuffers.pad_evaluation _ _ _ _ _ _ _).eqTrans
        (RationalBivariateGaussianEmbedding.bivariate_conjugacy G m a x y hG).eqSymm)
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) e

theorem add_evaluation (A B m a x y : PTm n) (hA : Γ ⊢[PRAAx] rowShape A m a) (hB : Γ ⊢[PRAAx] rowShape B m a) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (add A B m a) m x y ≐ RationalArithmetic.add
      (RationalBivariateGaussianEmbedding.bivariate A m x y) (RationalBivariateGaussianEmbedding.bivariate B m x y) := by
  let A' := RationalRowSpanGaussianEmbedding.matrix A m (succ a)
  let B' := RationalRowSpanGaussianEmbedding.matrix B m (succ a)
  have as : Γ ⊢[PRAAx] rowShape A' m a := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have bs : Γ ⊢[PRAAx] rowShape B' m a := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have ae : Γ ⊢[PRAAx] rowsEmbedded A A' m a := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have be : Γ ⊢[PRAAx] rowsEmbedded B B' m a := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have e := (RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (add A B m a) (GaussianBivariatePolynomialBuffers.add A' B' m a) m a x y
    (add_shape _ _ _ _) (.andE₁ (.andE₂ (GaussianBivariatePolynomialBuffers.add_stored _ _ _ _)))
    (add_rows_embedded _ _ _ _ _ _ ae be)).eqTrans
      ((GaussianBivariatePolynomialBuffers.add_evaluation _ _ _ _ _ _ as bs).eqTrans
        ((GaussianRationalSyntheticDivision.qadd_congr
          (RationalBivariateGaussianEmbedding.bivariate_conjugacy A m a x y hA).eqSymm
          (RationalBivariateGaussianEmbedding.bivariate_conjugacy B m a x y hB).eqSymm).eqTrans
            (RationalGaussianEmbedding.embed_add _ _).eqSymm))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.add_guard _ _) e

theorem scalar_pad_tail (C d s : PTm n) (hs : Γ ⊢[PRAAx] lt s (length C)) : Γ ⊢[PRAAx]
    entry (leftPad C d) (d+s) ≐ entry C s := by
  have range : Γ ⊢[PRAAx] lt (d+s) (d+length C) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] succ s+d ≐ succ (d+s)) (add_comm (length C) d) (add_le_add_right d hs)
  exact (RationalPolynomialBuffersGaussianEmbedding.pad_lookup C d (d+s) range).eqTrans
    ((RationalPolynomialBuffersGaussianEmbedding.pad_coefficient_after _ _ _ (le_add_right _ _)).eqTrans
      (entry_congr (.eqRefl _) ((congrMonus (add_comm d s) (.eqRefl d)).eqTrans (add_monus s d))))

theorem pad_leading_coefficient (G m a dx dy r s : PTm n) (hr : Γ ⊢[PRAAx] lt r dy)
    (hs : Γ ⊢[PRAAx] le s (a+dx)) : Γ ⊢[PRAAx] entry (entry (pad G m a dx dy) r) s ≐ RationalGaussianEmbedding.scalarZero :=
  (entry_congr ((pad_lookup _ _ _ _ _ _ (le_trans hr (le_add_right _ _))).eqTrans (pad_row_before _ _ _ _ _ hr)) (.eqRefl _)).eqTrans
    (RationalPolynomialBuffersGaussianEmbedding.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs))
theorem pad_tail_coefficient (G m a dx dy r s : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    entry (entry (pad G m a dx dy) (dy+r)) (dx+s) ≐ entry (normalizedRow (entry G r)) s := by
  have range : Γ ⊢[PRAAx] lt (dy+r) (dy+m) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] succ r+dy ≐ succ (dy+r)) (add_comm m dy) (add_le_add_right dy hr)
  have index : Γ ⊢[PRAAx] monus (dy+r) dy ≐ r := (congrMonus (add_comm dy r) (.eqRefl dy)).eqTrans (add_monus r dy)
  have padded : Γ ⊢[PRAAx] leftPad (normalizedRow (entry G (monus (dy+r) dy))) dx ≐ leftPad (normalizedRow (entry G r)) dx := by
    ipra_congr (leftPad (normalizedRow (entry (var 0) (var 1))) (var 2) : PTm 3) with [.eqRefl G, index, .eqRefl dx]
  have old := (pad_lookup G m a dx dy (dy+r) range).eqTrans
    ((pad_row_after G a dx dy (dy+r) (le_add_right _ _)).eqTrans padded)
  exact (entry_congr old (.eqRefl _)).eqTrans (scalar_pad_tail _ _ _
    (lt_congr (.eqRefl _) ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG hr)).eqSymm ((succ_monus_succ _ _).eqTrans hs)))


theorem normalized_pad_well_formed (C d s : PTm n) (hs : Γ ⊢[PRAAx] lt s (d+length C)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (leftPad (normalizedRow C) d) s) := by
  have range := lt_congr (.eqRefl _) (congrAdd (.eqRefl d) (normalized_length C)).eqSymm hs
  have read := RationalPolynomialBuffersGaussianEmbedding.pad_lookup (normalizedRow C) d s range
  refine .orE (lt_or_le s d) ?_ ?_
  · exact RationalArithmetic.guard_congr (read.wk.eqTrans (RationalPolynomialBuffersGaussianEmbedding.pad_coefficient_before _ _ _ Prf.hyp0))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · have tail := RationalPolynomialBuffersGaussianEmbedding.pad_tail_range (normalizedRow C) d s Prf.hyp0 range.wk
    have bound := lt_congr (.eqRefl _) (normalized_length C) tail
    exact RationalArithmetic.guard_congr
      (read.wk.eqTrans ((RationalPolynomialBuffersGaussianEmbedding.pad_coefficient_after _ _ _ Prf.hyp0).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.scaled_lookup C RationalGaussianEmbedding.scalarOne _ bound)))
      (RationalArithmetic.multiply_guard _ _)

theorem pad_coefficient_well_formed (G m a dx dy r s : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r (dy+m)) (hs : Γ ⊢[PRAAx] le s (a+dx)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (pad G m a dx dy) r) s) := by
  have read := pad_lookup G m a dx dy r hr
  refine .orE (lt_or_le r dy) ?_ ?_
  · exact RationalArithmetic.guard_congr
      ((entry_congr (read.wk.eqTrans (pad_row_before _ _ _ _ _ Prf.hyp0)) (.eqRefl _)).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs.wk)))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · let Δ := le dy r :: Γ
    have index := pad_tail_index m dy r (Γ := Δ) hr.wk Prf.hyp0
    have len := row_shape_at _ _ _ _ hG.wk index
    have range : Δ ⊢[PRAAx] lt s (dx+length (entry G (monus r dy))) :=
      lt_congr (.eqRefl _) ((congrAdd (.eqRefl dx) len).eqTrans (by ipra_ring)).eqSymm ((succ_monus_succ _ _).eqTrans hs.wk)
    exact RationalArithmetic.guard_congr
      (entry_congr (read.wk.eqTrans (pad_row_after _ _ _ _ _ Prf.hyp0)) (.eqRefl _))
      (normalized_pad_well_formed _ _ _ range)

theorem add_coefficient_well_formed (A B m a r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s a) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (add A B m a) r) s) :=
  RationalArithmetic.guard_congr (add_coefficient _ _ _ _ _ _ hr hs) (RationalArithmetic.add_guard _ _)


def padF : PR 5 := PTm.toPR (pad (var 0) (var 1) (var 2) (var 3) (var 4))
def addF : PR 4 := PTm.toPR (add (var 0) (var 1) (var 2) (var 3))
def padRun (G m a dx dy : PTm n) : PTm n := app padF ![G,m,a,dx,dy]
def addRun (A B m a : PTm n) : PTm n := app addF ![A,B,m,a]
theorem pad_program (G m a dx dy : PTm n) : Γ ⊢[PRAAx] padRun G m a dx dy ≐ pad G m a dx dy := by
  simpa [padRun,padF] using toPR_eq (Γ := Γ) (pad (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![G,m,a,dx,dy]
theorem add_program (A B m a : PTm n) : Γ ⊢[PRAAx] addRun A B m a ≐ add A B m a := by
  simpa [addRun,addF] using toPR_eq (Γ := Γ) (add (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,B,m,a]

theorem actual_rational_rectangular_pad_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (var 0) (var 1) (var 2) ⟶
      (length (pad (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 4+var 1 ⋏
        rowShape (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4+var 1) (var 2+var 3))) :=
  closeUniv 5 (.impI (.andI (pad_length _ _ _ _ _) (pad_shape _ _ _ _ _ Prf.hyp0)))
theorem actual_rational_rectangular_pad_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 2) (var 3) ⟶ rowShape (var 1) (var 2) (var 3) ⟶ rowsEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      rowsEmbedded (pad (var 0) (var 2) (var 3) (var 4) (var 5)) (GaussianBivariatePolynomialBuffers.pad (var 1) (var 2) (var 3) (var 4) (var 5))
        (var 5+var 2) (var 3+var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (pad_rows_embedded _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_rectangular_pad_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowShape (var 0) (var 1) (var 2) ⟶
      RationalBivariateGaussianEmbedding.bivariate (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4+var 1) (var 5) (var 6) ≐
        RationalBivariateGaussianEmbedding.bivariate (var 0) (var 1) (var 5) (var 6)) :=
  closeUniv 7 (.impI (pad_evaluation _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_rectangular_pad_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowShape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 1) ⟶ le (var 6) (var 2) ⟶
      entry (entry (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 4+var 5)) (var 3+var 6) ≐
        entry (normalizedRow (entry (var 0) (var 5))) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (pad_tail_coefficient _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_rectangular_add_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (add (var 0) (var 1) (var 2) (var 3)) ≐ var 2 ⋏ rowShape (add (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.andI (add_length _ _ _ _) (add_shape _ _ _ _))
theorem actual_rational_rectangular_add_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 2) ⟶ le (var 5) (var 3) ⟶ entry (entry (add (var 0) (var 1) (var 2) (var 3)) (var 4)) (var 5) ≐
      RationalArithmetic.add (entry (entry (var 0) (var 4)) (var 5)) (entry (entry (var 1) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (.impI (add_coefficient _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_rectangular_add_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 2) (var 3) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      RationalBivariateGaussianEmbedding.bivariate (add (var 0) (var 1) (var 2) (var 3)) (var 2) (var 4) (var 5) ≐ RationalArithmetic.add
        (RationalBivariateGaussianEmbedding.bivariate (var 0) (var 2) (var 4) (var 5))
        (RationalBivariateGaussianEmbedding.bivariate (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (add_evaluation _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_rectangular_pad_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (rowShape (var 0) (var 1) (var 2) ⟶ lt (var 5) (var 4+var 1) ⟶ le (var 6) (var 2+var 3) ⟶
      RationalNormalForm.wellFormed (entry (entry (pad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (pad_coefficient_well_formed _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_rectangular_pad_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (padRun (var 0) (var 1) (var 2) (var 3) (var 4) ≐ pad (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (pad_program _ _ _ _ _)
theorem actual_rational_rectangular_add_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (addRun (var 0) (var 1) (var 2) (var 3) ≐ add (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (add_program _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalBivariatePolynomialBuffersGaussianEmbedding
