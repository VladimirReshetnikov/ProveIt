import IPRADerivations.Analysis.Polynomials.Determinants.RationalEmbedding.RationalPolynomialDeterminantTermsGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.Rational.RationalBivariateGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMonicCompanion

/-!
# Actual original rational polynomial companion

All original rational operations are performed on actual stored coefficient
buffers. The descending Y shift appends a genuine zero row; normalization,
products and subtraction are original rational programs. No matrix law is
an input to the local coefficient transport.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialMonicCompanionGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarZero scalarOne)
open RationalPolynomialGaussianEmbedding (coefficients embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at data)
open RationalPolynomialDeterminantTermsGaussianEmbedding (entriesEqual entry_equal_at embedded_entries_to_codes coefficient_left_entries)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem embedded_at (C D H i : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D H) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    embed (entry C i) ≐ entry D i := by
  have rule : Γ ⊢[PRAAx] lt i H ⟶ embed (entry C i) ≐ entry D i := by
    simpa [RationalPolynomialBuffersGaussianEmbedding.embeddedEntries] using h.allE i
  exact .impE rule hi
theorem padded_codes_at (P Q H i : PTm n) (h : Γ ⊢[PRAAx] entriesEqual P Q H) : Γ ⊢[PRAAx]
    GaussianRationalLinearProduct.padded P H i ≐ GaussianRationalLinearProduct.padded Q H i := by
  refine .orE (lt_or_le i H) ?_ ?_
  · exact (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqTrans
      ((entry_equal_at _ _ _ _ h.wk Prf.hyp0).eqTrans (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqSymm)
  · exact (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqTrans
      (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqSymm
theorem product_transport (P Q P' Q' N M k : PTm n)
    (hp : Γ ⊢[PRAAx] embeddedEntries P P' (succ N)) (hq : Γ ⊢[PRAAx] embeddedEntries Q Q' (succ M))
    (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    embed (entry (RationalPolynomialProductGaussianEmbedding.product P Q N M) k) ≐
      entry (GaussianRationalPolynomialProduct.product P' Q' N M) k := by
  have pc := embedded_entries_to_codes _ _ _ hp
  have qc := embedded_entries_to_codes _ _ _ hq
  have qcs : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (coefficients (Syn.shift Q) (succ (Syn.shift M))) (Syn.shift Q') (succ (Syn.shift M)) := by
    simpa only [Fm.shift,RationalPolynomialDeterminantTermsGaussianEmbedding.subst_entriesEqual,
      RationalPolynomialGaussianEmbedding.subst_coefficients,ConciseIPRA.PTm.subst_succ,Syn.shift] using qc.shift
  have pads : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift k) ⟶
      GaussianRationalLinearProduct.padded (Syn.shift (coefficients Q (succ M))) (succ (Syn.shift M)) (var 0) ≐
        GaussianRationalLinearProduct.padded (Syn.shift Q') (succ (Syn.shift M)) (var 0)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,RationalPolynomialGaussianEmbedding.subst_coefficients,ConciseIPRA.PTm.subst_succ] using
      padded_codes_at (coefficients (Syn.shift Q) (succ (Syn.shift M))) (Syn.shift Q') (succ (Syn.shift M)) (var 0) qcs.wk
  exact (RationalPolynomialProductGaussianEmbedding.product_embedding P Q N M k hk).eqTrans
    ((GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ hk).eqTrans
      ((coefficient_left_entries _ _ _ M (succ N) (succ N) k pc (le_refl _)).eqTrans
        ((GaussianRationalMonicReconstruction.coefficient_padded_ext _ _ _ _ _ _ _ pads).eqTrans
          (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ hk).eqSymm)))

def normalizedRow (C : PTm n) : PTm n := RationalPolynomialBuffersGaussianEmbedding.scaled C scalarOne
def nextRow (G m a r : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus m (succ r)))
  (RationalPolynomialBuffersGaussianEmbedding.zeros (succ a)) (normalizedRow (entry G (succ r)))
def topRow (G : PTm n) : PTm n := normalizedRow (entry G zero)
def productRow (F G a c r : PTm n) : PTm n := RationalPolynomialProductGaussianEmbedding.product
  (topRow G) (normalizedRow (entry F r)) a c
def shiftedRow (G m a c r : PTm n) : PTm n := RationalPolynomialBuffersGaussianEmbedding.leftPad (nextRow G m a r) c
def differenceBody : PTm 2 := RationalArithmetic.add (entry (fstT (var 1)) (var 0))
  (RationalArithmetic.negative (entry (sndT (var 1)) (var 0)))
def difference (P Q H : PTm n) : PTm n := sequence differenceBody H (pairT P Q)
def outputRow (F G m a c r : PTm n) : PTm n := difference (shiftedRow G m a c r) (productRow F G a c r) (succ (a+c))
def rowF : PR 6 := PTm.toPR (outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def rowBody : PTm 2 := PTm.app rowF ![fstT (var 1),fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
  fstT (sndT (sndT (sndT (var 1)))),sndT (sndT (sndT (sndT (var 1)))),var 0]
def companion (F G m a c : PTm n) : PTm n := sequence rowBody m (data F G m a c)

ipra_subst normalizedRow
ipra_subst nextRow [Signum.sg]
ipra_subst topRow
ipra_subst productRow
ipra_subst shiftedRow
ipra_subst difference
ipra_subst outputRow
ipra_subst companion

theorem normalized_length (C : PTm n) : Γ ⊢[PRAAx] length (normalizedRow C) ≐ length C := RationalPolynomialBuffersGaussianEmbedding.scaled_length _ _
theorem next_inside (G m a r : PTm n) (hr : Γ ⊢[PRAAx] lt (succ r) m) : Γ ⊢[PRAAx]
    nextRow G m a r ≐ normalizedRow (entry G (succ r)) := RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem next_outside (G m a r : PTm n) (hr : Γ ⊢[PRAAx] le m (succ r)) : Γ ⊢[PRAAx]
    nextRow G m a r ≐ RationalPolynomialBuffersGaussianEmbedding.zeros (succ a) :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hr)
theorem next_length (G m a r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx] length (nextRow G m a r) ≐ succ a := by
  refine .orE (lt_or_le (succ r) m) ?_ ?_
  · exact (congrFst (next_inside _ _ _ _ Prf.hyp0)).eqTrans ((normalized_length _).eqTrans (row_shape_at _ _ _ _ hG.wk Prf.hyp0))
  · exact (congrFst (next_outside _ _ _ _ Prf.hyp0)).eqTrans (RationalPolynomialBuffersGaussianEmbedding.zeros_length _)
theorem difference_body_at (P Q i : PTm n) : Γ ⊢[PRAAx] inst2 differenceBody i (pairT P Q) ≐
    RationalArithmetic.add (entry P i) (RationalArithmetic.negative (entry Q i)) := by
  simp only [differenceBody,inst2,RationalArithmetic.subst_add,RationalArithmetic.subst_negative,Foundations.MasterCertificate.subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.add_congr (entry_congr (fst_pair _ _) (.eqRefl _))
    (RationalAlgebra.negative_congr (entry_congr (snd_pair _ _) (.eqRefl _)))
theorem difference_length (P Q H : PTm n) : Γ ⊢[PRAAx] length (difference P Q H) ≐ H := sequence_length _ _ _
theorem difference_lookup (P Q H i : PTm n) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    entry (difference P Q H) i ≐ RationalArithmetic.add (entry P i) (RationalArithmetic.negative (entry Q i)) :=
  (sequence_decode differenceBody hi).eqTrans (difference_body_at P Q i)
theorem output_length (F G m a c r : PTm n) : Γ ⊢[PRAAx] length (outputRow F G m a c r) ≐ succ (a+c) := difference_length _ _ _
theorem row_program (F G m a c r : PTm n) : Γ ⊢[PRAAx] PTm.app rowF ![F,G,m,a,c,r] ≐ outputRow F G m a c r := by
  simpa [rowF] using toPR_eq (Γ := Γ) (outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,G,m,a,c,r]
theorem row_body_at (F G m a c r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (data F G m a c) ≐ outputRow F G m a c r := by
  simp only [rowBody, inst2, ConciseIPRA.PTm.subst_app, subst_vecCons, subst_vecEmpty,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  have field (i : Fin 5) : Γ ⊢[PRAAx]
      pairVectorField 4 (data F G m a c) i ≐ ![F,G,m,a,c] i :=
    pairVectorField_eq 4 ![F,G,m,a,c] (.eqRefl _) i
  exact (congrApp rowF (fun i => by
    fin_cases i
    · exact field 0
    · exact field 1
    · exact field 2
    · exact field 3
    · exact field 4
    · exact .eqRefl _)).eqTrans (row_program F G m a c r)
theorem companion_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (companion F G m a c) ≐ m := sequence_length _ _ _
theorem companion_lookup (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (companion F G m a c) r ≐ outputRow F G m a c r := (sequence_decode rowBody hr).eqTrans (row_body_at F G m a c r)
theorem actual_row_length (F G m a c r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (companion F G m a c) r) ≐ succ (a+c) := (congrFst (companion_lookup _ _ _ _ _ _ hr)).eqTrans (output_length _ _ _ _ _ _)

theorem embedded_congr {C C' D D' H : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C') (hD : Γ ⊢[PRAAx] D ≐ D')
    (h : Γ ⊢[PRAAx] embeddedEntries C D H) : Γ ⊢[PRAAx] embeddedEntries C' D' H := by
  have out := Prf.eqSubst (Γ := Γ) (embeddedEntries (var 0) (var 1) (var 2) : Fm PTm 3)
    ![C,D,H] ![C',D',H] (fun i => by fin_cases i; exact hC; exact hD; exact .eqRefl _) (by simpa using h)
  simpa using out
theorem normalized_entry (C D H i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ H) (hD : Γ ⊢[PRAAx] length D ≐ H)
    (h : Γ ⊢[PRAAx] embeddedEntries C D H) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    embed (entry (normalizedRow C) i) ≐ entry (GaussianPolynomialMonicCompanion.normalizedRow D) i :=
  (embed_congr (RationalPolynomialBuffersGaussianEmbedding.scaled_lookup _ _ _ (lt_congr (.eqRefl _) hC.eqSymm hi))).eqTrans
    ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr RationalGaussianEmbedding.embed_one (embedded_at C D H i h hi)).eqTrans
        (GaussianRationalCoefficientScaling.scaled_lookup _ _ _ (lt_congr (.eqRefl _) hD.eqSymm hi)).eqSymm))
theorem normalized_entries (C D H : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ H) (hD : Γ ⊢[PRAAx] length D ≐ H)
    (h : Γ ⊢[PRAAx] embeddedEntries C D H) : Γ ⊢[PRAAx]
    embeddedEntries (normalizedRow C) (GaussianPolynomialMonicCompanion.normalizedRow D) H := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ Syn.shift H := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ Syn.shift H := by simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,Syn.shift] using hD.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] embeddedEntries (Syn.shift C) (Syn.shift D) (Syn.shift H) := by
    simpa only [Fm.shift,RationalPolynomialBuffersGaussianEmbedding.subst_embeddedEntries,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_normalizedRow,GaussianPolynomialMonicCompanion.subst_normalizedRow] using
    normalized_entry (Syn.shift C) (Syn.shift D) (Syn.shift H) (var 0) cs.wk ds.wk es.wk Prf.hyp0

theorem pad_transport (C D H t i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ H) (hD : Γ ⊢[PRAAx] length D ≐ H)
    (h : Γ ⊢[PRAAx] embeddedEntries C D H) (hi : Γ ⊢[PRAAx] lt i (t+H)) : Γ ⊢[PRAAx]
    embed (entry (RationalPolynomialBuffersGaussianEmbedding.leftPad C t) i) ≐ entry (GaussianRationalPolynomialBuffers.leftPad D t) i := by
  have rC := lt_congr (.eqRefl _) (congrAdd (.eqRefl t) hC).eqSymm hi
  have rD := lt_congr (.eqRefl _) (congrAdd (.eqRefl t) hD).eqSymm hi
  have middle : Γ ⊢[PRAAx] embed (RationalPolynomialBuffersGaussianEmbedding.padCoefficient C t i) ≐
      GaussianRationalPolynomialBuffers.padCoefficient D t i := by
    refine .orE (lt_or_le i t) ?_ ?_
    · exact (embed_congr (RationalPolynomialBuffersGaussianEmbedding.pad_coefficient_before _ _ _ Prf.hyp0)).eqTrans
        (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalPolynomialBuffers.pad_coefficient_before _ _ _ Prf.hyp0).eqSymm)
    · have tailRange := RationalPolynomialBuffersGaussianEmbedding.pad_tail_range C t i Prf.hyp0 rC.wk
      exact (embed_congr (RationalPolynomialBuffersGaussianEmbedding.pad_coefficient_after _ _ _ Prf.hyp0)).eqTrans
        ((embedded_at C D H _ h.wk (lt_congr (.eqRefl _) hC.wk tailRange)).eqTrans
          (GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ Prf.hyp0).eqSymm)
  exact (embed_congr (RationalPolynomialBuffersGaussianEmbedding.pad_lookup C t i rC)).eqTrans
    (middle.eqTrans (GaussianRationalPolynomialBuffers.pad_lookup D t i rD).eqSymm)

def rowsEmbedded (F F' m c : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  embeddedEntries (entry (Syn.shift F) (var 0)) (entry (Syn.shift F') (var 0)) (succ (Syn.shift c)))
ipra_subst rowsEmbedded [Syn.subst_shift, Syn.shift_subst]
theorem row_embedded_at (F F' m c r : PTm n) (h : Γ ⊢[PRAAx] rowsEmbedded F F' m c) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    embeddedEntries (entry F r) (entry F' r) (succ c) := by
  have gate : Γ ⊢[PRAAx] lt r m ⟶ embeddedEntries (entry F r) (entry F' r) (succ c) := by
    simpa [rowsEmbedded] using h.allE r
  exact .impE gate hr
theorem original_rows_embedded (F m c : PTm n) : Γ ⊢[PRAAx]
    rowsEmbedded F (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) m c := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,RationalRowSpanGaussianEmbedding.subst_matrix,ConciseIPRA.PTm.subst_succ] using
    RationalBivariateGaussianEmbedding.row_embedding (Syn.shift F) (Syn.shift m) (succ (Syn.shift c)) (var 0) Prf.hyp0

theorem next_entries (G G' m a r : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (he : Γ ⊢[PRAAx] rowsEmbedded G G' m a) : Γ ⊢[PRAAx]
    embeddedEntries (nextRow G m a r) (GaussianPolynomialMonicCompanion.nextRow G' m a r) (succ a) := by
  refine .orE (lt_or_le (succ r) m) ?_ ?_
  · exact embedded_congr (next_inside G m a r Prf.hyp0).eqSymm (GaussianPolynomialMonicCompanion.next_inside G' m a r Prf.hyp0).eqSymm
      (normalized_entries _ _ _ (row_shape_at _ _ _ _ hG.wk Prf.hyp0) (row_shape_at _ _ _ _ hG'.wk Prf.hyp0)
        (row_embedded_at _ _ _ _ _ he.wk Prf.hyp0))
  · exact embedded_congr (next_outside G m a r Prf.hyp0).eqSymm (GaussianPolynomialMonicCompanion.next_outside G' m a r Prf.hyp0).eqSymm
      (RationalPolynomialBuffersGaussianEmbedding.zeros_embedded_entries (succ a))

theorem output_entry_transport (F F' G G' m a c r s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hF' : Γ ⊢[PRAAx] rowShape F' m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (heF : Γ ⊢[PRAAx] rowsEmbedded F F' m c) (heG : Γ ⊢[PRAAx] rowsEmbedded G G' m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    embed (entry (outputRow F G m a c r) s) ≐ entry (GaussianPolynomialMonicCompanion.outputRow F' G' m a c r) s := by
  have top := normalized_entries _ _ _ (row_shape_at G m a zero hG hm) (row_shape_at G' m a zero hG' hm)
    (row_embedded_at G G' m a zero heG hm)
  have factor := normalized_entries _ _ _ (row_shape_at F m c r hF hr) (row_shape_at F' m c r hF' hr)
    (row_embedded_at F F' m c r heF hr)
  have prod := product_transport (topRow G) (normalizedRow (entry F r)) (GaussianPolynomialMonicCompanion.topRow G')
    (GaussianPolynomialMonicCompanion.normalizedRow (entry F' r)) a c s top factor hs
  have range : Γ ⊢[PRAAx] lt s (c+succ a) :=
    le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (a+c) ≐ c+succ a) ((succ_monus_succ _ _).eqTrans hs)
  have shifted := pad_transport (nextRow G m a r) (GaussianPolynomialMonicCompanion.nextRow G' m a r) (succ a) c s
    (next_length G m a r hG) (GaussianPolynomialMonicCompanion.next_length G' m a r hG')
    (next_entries G G' m a r hG hG' heG) range
  have original := (embed_congr (difference_lookup (shiftedRow G m a c r) (productRow F G a c r) (succ (a+c)) s
    ((succ_monus_succ _ _).eqTrans hs))).eqTrans (RationalGaussianEmbedding.embed_add _ _)
  have move := GaussianRationalSyntheticDivision.qadd_congr shifted
    ((RationalGaussianEmbedding.embed_negative _).eqTrans (RationalGaussianEmbedding.negative_congr prod))
  exact original.eqTrans (move.eqTrans (GaussianCoefficientL1.sub_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)).eqSymm)

theorem companion_entry_transport (F F' G G' m a c r s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hF' : Γ ⊢[PRAAx] rowShape F' m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hG' : Γ ⊢[PRAAx] rowShape G' m a)
    (heF : Γ ⊢[PRAAx] rowsEmbedded F F' m c) (heG : Γ ⊢[PRAAx] rowsEmbedded G G' m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    embed (entry (entry (companion F G m a c) r) s) ≐
      entry (entry (GaussianPolynomialMonicCompanion.companion F' G' m a c) r) s :=
  (embed_congr (entry_congr (companion_lookup F G m a c r hr) (.eqRefl s))).eqTrans
    ((output_entry_transport F F' G G' m a c r s hm hF hF' hG hG' heF heG hr hs).eqTrans
      (entry_congr (GaussianPolynomialMonicCompanion.companion_lookup F' G' m a c r hr) (.eqRefl s)).eqSymm)

theorem original_entry_embedding (F G m a c r s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    embed (entry (entry (companion F G m a c) r) s) ≐ entry (entry (GaussianPolynomialMonicCompanion.companion
      (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c) r) s :=
  companion_entry_transport F _ G _ m a c r s hm hF (RationalBivariateGaussianEmbedding.embedded_row_shape F m c)
    hG (RationalBivariateGaussianEmbedding.embedded_row_shape G m a) (original_rows_embedded F m c) (original_rows_embedded G m a) hr hs

def transportInput (F F' G G' m a c : PTm n) : Fm PTm n := le one m ⋏
  (rowShape F m c ⋏ (rowShape F' m c ⋏ (rowShape G m a ⋏ (rowShape G' m a ⋏
    (rowsEmbedded F F' m c ⋏ rowsEmbedded G G' m a)))))
ipra_subst transportInput
theorem companion_entry_from_input (F F' G G' m a c r s : PTm n)
    (h : Γ ⊢[PRAAx] transportInput F F' G G' m a c) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    embed (entry (entry (companion F G m a c) r) s) ≐ entry (entry (GaussianPolynomialMonicCompanion.companion F' G' m a c) r) s :=
  companion_entry_transport F F' G G' m a c r s (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) (.andE₁ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))))
      (.andE₁ (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))))) hr hs
theorem companion_row_entries (F F' G G' m a c r : PTm n)
    (h : Γ ⊢[PRAAx] transportInput F F' G G' m a c) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    embeddedEntries (entry (companion F G m a c) r) (entry (GaussianPolynomialMonicCompanion.companion F' G' m a c) r) (succ (a+c)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] transportInput (Syn.shift F) (Syn.shift F') (Syn.shift G) (Syn.shift G')
      (Syn.shift m) (Syn.shift a) (Syn.shift c) := by simpa only [Fm.shift,subst_transportInput,Syn.shift] using h.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (Syn.shift a+Syn.shift c)) :: Γ.map Fm.shift ⊢[PRAAx] le (var 0) (Syn.shift a+Syn.shift c) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_companion,GaussianPolynomialMonicCompanion.subst_companion,Foundations.MasterCertificate.subst_entry,
    ConciseIPRA.PTm.subst_succ,PTm.subst_add] using companion_entry_from_input
      (Syn.shift F) (Syn.shift F') (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift r) (var 0) hs.wk rs.wk bound
theorem companion_rows_embedded (F F' G G' m a c : PTm n)
    (h : Γ ⊢[PRAAx] transportInput F F' G G' m a c) : Γ ⊢[PRAAx]
    rowsEmbedded (companion F G m a c) (GaussianPolynomialMonicCompanion.companion F' G' m a c) m (a+c) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] transportInput (Syn.shift F) (Syn.shift F') (Syn.shift G) (Syn.shift G')
      (Syn.shift m) (Syn.shift a) (Syn.shift c) := by simpa only [Fm.shift,subst_transportInput,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_companion,GaussianPolynomialMonicCompanion.subst_companion,PTm.subst_add] using companion_row_entries
    (Syn.shift F) (Syn.shift F') (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) hs.wk Prf.hyp0
theorem companion_row_shape (F G m a c : PTm n) : Γ ⊢[PRAAx] rowShape (companion F G m a c) m (a+c) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_companion,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    actual_row_length (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) Prf.hyp0

theorem output_coefficient_well_formed (F G m a c r s : PTm n) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (outputRow F G m a c r) s) :=
  RationalArithmetic.guard_congr (difference_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)) (RationalArithmetic.add_guard _ _)
def companionF : PR 5 := PTm.toPR (companion (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := PTm.app companionF ![F,G,m,a,c]
ipra_subst run
theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ companion F G m a c := by
  simpa only [run,companionF,subst_companion,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (companion (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (run F G m a c) ≐ m :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (companion_length _ _ _ _ _)
theorem returned_entry_embedding (F G m a c r s : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hF : Γ ⊢[PRAAx] rowShape F m c) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+c)) : Γ ⊢[PRAAx]
    embed (entry (entry (run F G m a c) r) s) ≐ entry (entry (GaussianPolynomialMonicCompanion.companion
      (RationalRowSpanGaussianEmbedding.matrix F m (succ c)) (RationalRowSpanGaussianEmbedding.matrix G m (succ a)) m a c) r) s :=
  (embed_congr (entry_congr (entry_congr (program_at F G m a c) (.eqRefl r)) (.eqRefl s))).eqTrans
    (original_entry_embedding F G m a c r s hm hF hG hr hs)

theorem actual_rational_companion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ companion (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_rational_companion_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 2) := closeUniv 5 (returned_length _ _ _ _ _)
theorem actual_rational_companion_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 2) ⟶ entry (companion (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
      outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (.impI (companion_lookup _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_companion_row_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rowShape (companion (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 3+var 4)) :=
  closeUniv 5 (companion_row_shape _ _ _ _ _)
theorem actual_rational_companion_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      lt (var 5) (var 2) ⟶ le (var 6) (var 3+var 4) ⟶
        embed (entry (entry (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (var 6)) ≐ entry (entry
          (GaussianPolynomialMonicCompanion.companion (RationalRowSpanGaussianEmbedding.matrix (var 0) (var 2) (succ (var 4)))
            (RationalRowSpanGaussianEmbedding.matrix (var 1) (var 2) (succ (var 3))) (var 2) (var 3) (var 4)) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (returned_entry_embedding _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_rational_companion_final_zero_branch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (succ (var 3)) ⟶ nextRow (var 0) (var 1) (var 2) (var 3) ≐ RationalPolynomialBuffersGaussianEmbedding.zeros (succ (var 2))) :=
  closeUniv 4 (.impI (next_outside _ _ _ _ Prf.hyp0))
theorem actual_rational_companion_output_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 6) (var 3+var 4) ⟶ RationalNormalForm.wellFormed (entry (outputRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6))) :=
  closeUniv 7 (.impI (output_coefficient_well_formed _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialMonicCompanionGaussianEmbedding
