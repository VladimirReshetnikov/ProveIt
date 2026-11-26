import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.RationalBivariatePolynomialBuffersGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariateMonicFactor

/-!
# The actual original rational full monic factor

The leading Y row is an actual original rational constant-one X buffer;
the actual original tail rows are retained. Its coefficient transport and
original two-variable evaluation recover the original monic evaluator.
The shared singleton is only a numerical list constructor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBivariateMonicFactorGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarOne)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (leftPad embeddedEntries)
open RationalPolynomialMonicCompanionGaussianEmbedding (rowsEmbedded row_embedded_at embedded_at)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def monicRow (c : PTm n) : PTm n := leftPad (singleton scalarOne) c
ipra_subst monicRow
theorem monic_row_length (c : PTm n) : Γ ⊢[PRAAx] length (monicRow c) ≐ succ c :=
  (RationalPolynomialBuffersGaussianEmbedding.pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) (singleton_length _)).eqTrans (by ipra_ring))

def row (F c i : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg i) (monicRow c) (entry F (pred i))

def rowBody : PTm 2 := row (fstT (var 1)) (sndT (var 1)) (var 0)

def table (F m c : PTm n) : PTm n := sequence rowBody (succ m) (pairT F c)

ipra_subst row [Signum.sg]

ipra_subst table

theorem row_body_at (F c i : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (pairT F c) ≐ row F c i := by
  simp only [rowBody, inst2, subst_row, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ipra_congr (row (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl i]

theorem table_length (F m c : PTm n) : Γ ⊢[PRAAx] length (table F m c) ≐ succ m := sequence_length _ _ _

theorem table_lookup (F m c i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ m)) :
    Γ ⊢[PRAAx] entry (table F m c) i ≐ row F c i :=
  (sequence_decode rowBody (x := pairT F c) hi).eqTrans (row_body_at F c i)

theorem table_head (F m c : PTm n) :
    Γ ⊢[PRAAx] entry (table F m c) zero ≐ monicRow c :=
  (table_lookup F m c zero (zero_lt_succ m)).eqTrans (RationalArithmetic.select_zero _ _ _ Signum.sg_zero)

theorem table_tail (F m c i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] entry (table F m c) (succ i) ≐ entry F i :=
  (table_lookup F m c (succ i) ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    ((RationalArithmetic.select_one _ _ _ (Signum.sg_succ i)).eqTrans (entry_congr (.eqRefl F) (pred_succ i)))

theorem table_row_length (F m c i : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hi : Γ ⊢[PRAAx] lt i (succ m)) : Γ ⊢[PRAAx] length (entry (table F m c) i) ≐ succ c := by
  refine .orE (zero_or_succ i) ?_ ?_
  · exact (congrFst ((entry_congr (.eqRefl (table F m c)) Prf.hyp0).eqTrans (table_head _ _ _))).eqTrans
      (monic_row_length c)
  · let Δ := (i ≐ succ (pred i)) :: Γ
    have below : Δ ⊢[PRAAx] lt (succ (pred i)) (succ m) :=
      lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] i ≐ succ (pred i)) (.eqRefl _) hi.wk
    have bound : Δ ⊢[PRAAx] lt (pred i) m :=
      (succ_monus_succ (succ (pred i)) m).eqSymm.eqTrans below
    exact (congrFst ((entry_congr (.eqRefl (table F m c)) Prf.hyp0).eqTrans (table_tail F m c (pred i) bound))).eqTrans
      (row_shape_at F m c (pred i) hF.wk bound)

theorem table_shape (F m c : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) :
    Γ ⊢[PRAAx] rowShape (table F m c) (succ m) c := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
    simpa [Fm.shift, Syn.shift] using hF.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_table, ConciseIPRA.PTm.subst_succ] using
    table_row_length (Syn.shift F) (Syn.shift m) (Syn.shift c) (var 0) hs.wk Prf.hyp0

theorem singleton_one_entries : Γ ⊢[PRAAx] embeddedEntries (singleton (scalarOne : PTm n)) (singleton GaussianRationalReciprocal.qone) one := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) one :: Γ.map Fm.shift
  have index : Δ ⊢[PRAAx] var 0 ≐ zero :=
    le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ zero))) (zero_le _)
  simpa only [Δ,Syn.shift,GaussianRationalMonicReduction.subst_singleton,RationalGaussianEmbedding.subst_scalarOne,
    GaussianRationalReciprocal.subst_qone,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    (embed_congr ((entry_congr (.eqRefl _) index).eqTrans (singleton_lookup scalarOne))).eqTrans
      (RationalGaussianEmbedding.embed_one.eqTrans
        ((singleton_lookup GaussianRationalReciprocal.qone).eqSymm.eqTrans (entry_congr (.eqRefl _) index).eqSymm))

theorem target_monic_row (c : PTm n) : Γ ⊢[PRAAx] GaussianPolynomialMonicCompanion.monicRow c ≐
    GaussianRationalPolynomialBuffers.leftPad (singleton GaussianRationalReciprocal.qone) c := by
  unfold GaussianPolynomialMonicCompanion.monicRow GaussianRationalMonicReduction.constant
  ipra_congr (GaussianRationalPolynomialBuffers.leftPad (var 0) (var 1) : PTm 2) with
    [.eqRefl (singleton GaussianRationalReciprocal.qone), pred_succ _] using [GaussianRationalSyntheticDivision.qone,
      GaussianRationalReciprocal.qone]

theorem monic_row_embedding (c s : PTm n) (hs : Γ ⊢[PRAAx] le s c) : Γ ⊢[PRAAx]
    embed (entry (monicRow c) s) ≐ entry (GaussianPolynomialMonicCompanion.monicRow c) s :=
  (RationalPolynomialMonicCompanionGaussianEmbedding.pad_transport _ _ one c s
    (singleton_length _) (singleton_length _) singleton_one_entries
    (lt_congr (.eqRefl _) (by ipra_ring) ((succ_monus_succ _ _).eqTrans hs))).eqTrans
      (entry_congr (target_monic_row c) (.eqRefl _)).eqSymm

theorem table_entry_transport (F F' m c r s : PTm n) (he : Γ ⊢[PRAAx] rowsEmbedded F F' m c)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) (hs : Γ ⊢[PRAAx] le s c) : Γ ⊢[PRAAx]
    embed (entry (entry (table F m c) r) s) ≐ entry (entry (GaussianBivariateMonicFactor.table F' m c) r) s := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact (embed_congr (entry_congr ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (table_head _ _ _)) (.eqRefl _))).eqTrans
      ((monic_row_embedding _ _ hs.wk).eqTrans
        (entry_congr ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianBivariateMonicFactor.table_head _ _ _)) (.eqRefl _)).eqSymm)
  · let Δ := (r ≐ succ (pred r)) :: Γ
    have bound : Δ ⊢[PRAAx] lt (pred r) m := (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (Prf.hyp0 : Δ ⊢[PRAAx] r ≐ succ (pred r)) (.eqRefl _) hr.wk)
    exact (embed_congr (entry_congr ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (table_tail _ _ _ _ bound)) (.eqRefl _))).eqTrans
      ((embedded_at _ _ _ _ (row_embedded_at _ _ _ _ _ he.wk bound) ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans
        (entry_congr ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianBivariateMonicFactor.table_tail _ _ _ _ bound)) (.eqRefl _)).eqSymm)

theorem table_row_entries (F F' m c r : PTm n) (he : Γ ⊢[PRAAx] rowsEmbedded F F' m c)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) : Γ ⊢[PRAAx]
    embeddedEntries (entry (table F m c) r) (entry (GaussianBivariateMonicFactor.table F' m c) r) (succ c) := by
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift F) (Syn.shift F') (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using he.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (succ (Syn.shift m)) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift c)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift c) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift c)))
  simpa only [Δ,Syn.shift,subst_table,GaussianBivariateMonicFactor.subst_table,subst_entry,ConciseIPRA.PTm.subst_succ] using
    table_entry_transport (Syn.shift F) (Syn.shift F') (Syn.shift m) (Syn.shift c) (Syn.shift r) (var 0) es.wk rs.wk bound

theorem table_rows_embedded (F F' m c : PTm n) (he : Γ ⊢[PRAAx] rowsEmbedded F F' m c) : Γ ⊢[PRAAx]
    rowsEmbedded (table F m c) (GaussianBivariateMonicFactor.table F' m c) (succ m) c := by
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift F) (Syn.shift F') (Syn.shift m) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_table,GaussianBivariateMonicFactor.subst_table,ConciseIPRA.PTm.subst_succ] using
    table_row_entries (Syn.shift F) (Syn.shift F') (Syn.shift m) (Syn.shift c) (var 0) es.wk Prf.hyp0

theorem table_evaluation (F m c x y : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (table F m c) (succ m) x y ≐ RationalBivariateGaussianEmbedding.monic F m x y := by
  let F' := RationalRowSpanGaussianEmbedding.matrix F m (succ c)
  have fs : Γ ⊢[PRAAx] rowShape F' m c := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have he : Γ ⊢[PRAAx] rowsEmbedded F F' m c := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have e := (RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (table F m c) (GaussianBivariateMonicFactor.table F' m c) (succ m) c x y
    (table_shape _ _ _ hF) (GaussianBivariateMonicFactor.table_shape _ _ _ fs) (table_rows_embedded _ _ _ _ he)).eqTrans
      ((GaussianBivariateMonicFactor.table_evaluation _ _ _ _ _).eqTrans (RationalBivariateGaussianEmbedding.monic_conjugacy F m c x y hF).eqSymm)
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) e

def tableF : PR 3 := PTm.toPR (table (var 0) (var 1) (var 2))
def run (F m c : PTm n) : PTm n := PTm.app tableF ![F,m,c]
ipra_subst run
theorem program_at (F m c : PTm n) : Γ ⊢[PRAAx] run F m c ≐ table F m c := by
  simpa [run,tableF] using toPR_eq (Γ := Γ) (table (var 0) (var 1) (var 2) : PTm 3) ![F,m,c]

theorem actual_rational_monic_factor_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowShape (var 0) (var 1) (var 2) ⟶
      (length (table (var 0) (var 1) (var 2)) ≐ succ (var 1) ⋏ rowShape (table (var 0) (var 1) (var 2)) (succ (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.andI (table_length _ _ _) (table_shape _ _ _ Prf.hyp0)))
theorem actual_rational_monic_factor_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (table (var 0) (var 1) (var 2)) zero ≐ monicRow (var 2) ⋏ length (monicRow (var 2)) ≐ succ (var 2)) :=
  closeUniv 3 (.andI (table_head _ _ _) (monic_row_length _))
theorem actual_rational_monic_factor_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ entry (table (var 0) (var 1) (var 2)) (succ (var 3)) ≐ entry (var 0) (var 3)) :=
  closeUniv 4 (.impI (table_tail _ _ _ _ Prf.hyp0))
theorem actual_rational_monic_factor_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowsEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      rowsEmbedded (table (var 0) (var 2) (var 3)) (GaussianBivariateMonicFactor.table (var 1) (var 2) (var 3)) (succ (var 2)) (var 3)) :=
  closeUniv 4 (.impI (table_rows_embedded _ _ _ _ Prf.hyp0))
theorem actual_rational_monic_factor_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (var 0) (var 1) (var 2) ⟶
      RationalBivariateGaussianEmbedding.bivariate (table (var 0) (var 1) (var 2)) (succ (var 1)) (var 3) (var 4) ≐
        RationalBivariateGaussianEmbedding.monic (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (table_evaluation _ _ _ _ _ Prf.hyp0))
theorem actual_rational_monic_factor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ table (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.RationalBivariateMonicFactorGaussianEmbedding
