import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialBuffers
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Original rational coefficient buffers and literal Gaussian transport

The actual stored buffers use original rational zero, addition and scalar
multiplication. Their individual embedded coefficient codes agree with the
existing Gaussian buffers. Raw input tails remain raw before embedding;
no outer list-code equality or evaluation identity is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialBuffersGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup coefficients_length embed_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zerosBody : PTm 2 := scalarZero
def zeros (L : PTm n) : PTm n := sequence zerosBody L zero
def padded (C L i : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus L i)) scalarZero (entry C i)
def addBody : PTm 2 := RationalArithmetic.add (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def added (C D L : PTm n) : PTm n := sequence addBody L (pairT C D)
def scaleBody : PTm 2 := RationalArithmetic.multiply (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def scaled (C s : PTm n) : PTm n := sequence scaleBody (length C) (pairT s C)
def padCoefficient (C t i : PTm n) : PTm n := RationalArithmetic.select
  (Signum.sg (monus t i)) (entry C (monus i t)) scalarZero
def padData (C t : PTm n) : PTm n := pairT C t
def padBody : PTm 2 := padCoefficient (fstT (var 1)) (sndT (var 1)) (var 0)
def leftPad (C t : PTm n) : PTm n := sequence padBody (t+length C) (padData C t)

ipra_subst zeros
ipra_subst padded [Signum.sg]
ipra_subst added
ipra_subst scaled
ipra_subst padCoefficient [Signum.sg]
ipra_subst padData
ipra_subst leftPad

theorem zeros_length (L : PTm n) : Γ ⊢[PRAAx] length (zeros L) ≐ L := sequence_length _ _ _
theorem zeros_lookup (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx] entry (zeros L) i ≐ scalarZero := by
  simpa only [zeros,zerosBody,inst2,RationalGaussianEmbedding.subst_scalarZero] using
    sequence_decode (Γ := Γ) zerosBody (x := zero) hi
theorem padded_inside (C L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx] padded C L i ≐ entry C i :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem padded_outside (C L i : PTm n) (hi : Γ ⊢[PRAAx] le L i) : Γ ⊢[PRAAx] padded C L i ≐ scalarZero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)
theorem added_length (C D L : PTm n) : Γ ⊢[PRAAx] length (added C D L) ≐ L := sequence_length _ _ _
theorem add_body_at (C D i : PTm n) : Γ ⊢[PRAAx]
    inst2 addBody i (pairT C D) ≐ RationalArithmetic.add (entry C i) (entry D i) := by
  simp only [addBody,inst2,RationalArithmetic.subst_add,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.add_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem added_lookup (C D L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    entry (added C D L) i ≐ RationalArithmetic.add (entry C i) (entry D i) :=
  (sequence_decode addBody hi).eqTrans (add_body_at C D i)
theorem scaled_length (C s : PTm n) : Γ ⊢[PRAAx] length (scaled C s) ≐ length C := sequence_length _ _ _
theorem scale_body_at (C s i : PTm n) : Γ ⊢[PRAAx]
    inst2 scaleBody i (pairT s C) ≐ RationalArithmetic.multiply s (entry C i) := by
  simp only [scaleBody,inst2,RationalArithmetic.subst_multiply,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.multiply_congr (fst_pair _ _) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem scaled_lookup (C s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    entry (scaled C s) i ≐ RationalArithmetic.multiply s (entry C i) :=
  (sequence_decode scaleBody hi).eqTrans (scale_body_at C s i)

theorem pad_coefficient_before (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx] padCoefficient C t i ≐ scalarZero :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem pad_coefficient_after (C t i : PTm n) (hi : Γ ⊢[PRAAx] le t i) : Γ ⊢[PRAAx] padCoefficient C t i ≐ entry C (monus i t) :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)
theorem pad_coefficient_congr {C D t u i j : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (ht : Γ ⊢[PRAAx] t ≐ u) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] padCoefficient C t i ≐ padCoefficient D u j := by
  ipra_congr (padCoefficient (var 0) (var 1) (var 2) : PTm 3) with [hC, ht, hi]
theorem pad_body_at (C t i : PTm n) : Γ ⊢[PRAAx] inst2 padBody i (padData C t) ≐ padCoefficient C t i := by
  simp only [padBody,inst2,subst_padCoefficient,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact pad_coefficient_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
theorem pad_length (C t : PTm n) : Γ ⊢[PRAAx] length (leftPad C t) ≐ t+length C := sequence_length _ _ _
theorem pad_lookup (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i (t+length C)) : Γ ⊢[PRAAx]
    entry (leftPad C t) i ≐ padCoefficient C t i := (sequence_decode padBody hi).eqTrans (pad_body_at C t i)

theorem zeros_embedding (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    embed (entry (zeros L) i) ≐ entry (GaussianRationalPolynomialBuffers.zeros L) i :=
  (embed_congr (zeros_lookup L i hi)).eqTrans (RationalGaussianEmbedding.embed_zero.eqTrans
    (GaussianRationalPolynomialBuffers.zeros_lookup L i hi).eqSymm)
theorem padded_embedding (C L i : PTm n) : Γ ⊢[PRAAx]
    embed (padded C L i) ≐ GaussianRationalLinearProduct.padded (coefficients C L) L i := by
  refine .orE (lt_or_le i L) ?_ ?_
  · exact (embed_congr (padded_inside C L i Prf.hyp0)).eqTrans
      ((coefficient_lookup C L i Prf.hyp0).eqSymm.eqTrans (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqSymm)
  · exact (embed_congr (padded_outside C L i Prf.hyp0)).eqTrans
      (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqSymm)
theorem added_embedding (C D L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    embed (entry (added C D L) i) ≐
      entry (GaussianRationalPolynomialBuffers.added (coefficients C L) (coefficients D L) L) i :=
  (embed_congr (added_lookup C D L i hi)).eqTrans ((RationalGaussianEmbedding.embed_add _ _).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr (coefficient_lookup C L i hi).eqSymm
      (coefficient_lookup D L i hi).eqSymm).eqTrans (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ hi).eqSymm))
theorem scaled_embedding (C s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    embed (entry (scaled C s) i) ≐ entry (GaussianRationalCoefficientScaling.scaled (coefficients C (length C)) (embed s)) i :=
  (embed_congr (scaled_lookup C s i hi)).eqTrans ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (coefficient_lookup C _ i hi).eqSymm).eqTrans
      (GaussianRationalCoefficientScaling.scaled_lookup _ _ _
        (lt_congr (.eqRefl _) (coefficients_length C (length C)).eqSymm hi)).eqSymm))

theorem pad_tail_range (C t i : PTm n) (ht : Γ ⊢[PRAAx] le t i)
    (hi : Γ ⊢[PRAAx] lt i (t+length C)) : Γ ⊢[PRAAx] lt (monus i t) (length C) := by
  apply le_of_eq_add (d := monus (t+length C) (succ i))
  ipra_lc natEq (eq_add_of_le hi)+natEq (eq_add_of_le ht)
theorem pad_embedding (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i (t+length C)) : Γ ⊢[PRAAx]
    embed (entry (leftPad C t) i) ≐ entry (GaussianRationalPolynomialBuffers.leftPad (coefficients C (length C)) t) i := by
  have gRange := lt_congr (.eqRefl _) (congrAdd (.eqRefl t) (coefficients_length C (length C))).eqSymm hi
  have middle : Γ ⊢[PRAAx] embed (padCoefficient C t i) ≐
      GaussianRationalPolynomialBuffers.padCoefficient (coefficients C (length C)) t i := by
    refine .orE (lt_or_le i t) ?_ ?_
    · exact (embed_congr (pad_coefficient_before C t i Prf.hyp0)).eqTrans
        (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalPolynomialBuffers.pad_coefficient_before _ _ _ Prf.hyp0).eqSymm)
    · exact (embed_congr (pad_coefficient_after C t i Prf.hyp0)).eqTrans
        ((coefficient_lookup C _ _ (pad_tail_range C t i Prf.hyp0 hi.wk)).eqSymm.eqTrans
          (GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ Prf.hyp0).eqSymm)
  exact (embed_congr (pad_lookup C t i hi)).eqTrans
    (middle.eqTrans (GaussianRationalPolynomialBuffers.pad_lookup _ _ _ gRange).eqSymm)

def embeddedEntries (C D L : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift L) ⟶
  embed (entry (Syn.shift C) (var 0)) ≐ entry (Syn.shift D) (var 0))
ipra_subst embeddedEntries [Syn.subst_shift, Syn.shift_subst]

theorem zeros_embedded_entries (L : PTm n) : Γ ⊢[PRAAx]
    embeddedEntries (zeros L) (GaussianRationalPolynomialBuffers.zeros L) L := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_zeros,GaussianRationalPolynomialBuffers.subst_zeros] using
    zeros_embedding (Syn.shift L) (var 0) Prf.hyp0
theorem added_embedded_entries (C D L : PTm n) : Γ ⊢[PRAAx]
    embeddedEntries (added C D L) (GaussianRationalPolynomialBuffers.added (coefficients C L) (coefficients D L) L) L := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_added,GaussianRationalPolynomialBuffers.subst_added,RationalPolynomialGaussianEmbedding.subst_coefficients] using
    added_embedding (Syn.shift C) (Syn.shift D) (Syn.shift L) (var 0) Prf.hyp0
theorem scaled_embedded_entries (C s : PTm n) : Γ ⊢[PRAAx]
    embeddedEntries (scaled C s) (GaussianRationalCoefficientScaling.scaled (coefficients C (length C)) (embed s)) (length C) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_scaled,GaussianRationalCoefficientScaling.subst_scaled,RationalPolynomialGaussianEmbedding.subst_coefficients,
    Foundations.SequenceComposition.subst_length,RationalGaussianEmbedding.subst_embed] using
    scaled_embedding (Syn.shift C) (Syn.shift s) (var 0) Prf.hyp0
theorem pad_embedded_entries (C t : PTm n) : Γ ⊢[PRAAx]
    embeddedEntries (leftPad C t) (GaussianRationalPolynomialBuffers.leftPad (coefficients C (length C)) t) (t+length C) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_leftPad,GaussianRationalPolynomialBuffers.subst_leftPad,RationalPolynomialGaussianEmbedding.subst_coefficients,
    Foundations.SequenceComposition.subst_length,PTm.subst_add] using pad_embedding (Syn.shift C) (Syn.shift t) (var 0) Prf.hyp0

theorem evaluation_transport (C D L z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L)
    (hD : Γ ⊢[PRAAx] length D ≐ L) (h : Γ ⊢[PRAAx] embeddedEntries C D L) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate C z) ≐ GaussianRationalHorner.evaluate D (embed z) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] embeddedEntries (Syn.shift C) (Syn.shift D) (Syn.shift L) := by
    simpa only [Fm.shift,subst_embeddedEntries,Syn.shift] using h.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift L) ⟶
      entry (Syn.shift (coefficients C L)) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift
    have rule : Δ ⊢[PRAAx] lt (var 0) (Syn.shift L) ⟶ embed (entry (Syn.shift C) (var 0)) ≐ entry (Syn.shift D) (var 0) := by
      simpa only [embeddedEntries,Fm.subst_imp,Fm.subst_eq,subst_lt,RationalGaussianEmbedding.subst_embed,
        Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.wk.allE (var 0)
    simpa only [Δ,Syn.shift,RationalPolynomialGaussianEmbedding.subst_coefficients] using
      (coefficient_lookup (Syn.shift C) (Syn.shift L) (var 0) (Γ := Δ) Prf.hyp0).eqTrans (.impE rule Prf.hyp0)
  exact (embed_congr (congrAp3 RationalPolynomialGaussianEmbedding.hornerF hC (.eqRefl _) (.eqRefl _))).eqTrans
    ((RationalPolynomialGaussianEmbedding.horner_conjugacy C z L L (le_refl _)).eqTrans
      ((GaussianRationalLinearProduct.horner_ext _ _ _ _ _ entries (le_refl _)).eqTrans
        (congrAp3 GaussianRationalHorner.hornerF hD.eqSymm (.eqRefl _) (.eqRefl _))))

theorem evaluation_at_width (C L z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate C z) ≐ GaussianRationalHorner.evaluate (coefficients C L) (embed z) := by
  refine evaluation_transport C (coefficients C L) L z hC (coefficients_length C L) ?_
  refine .allI (.impI ?_)
  simpa only [Syn.shift,RationalPolynomialGaussianEmbedding.subst_coefficients] using
    (coefficient_lookup (Syn.shift C) (Syn.shift L) (var 0) Prf.hyp0).eqSymm

theorem canonical_equal_of_embedding (a b : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a)
    (hb : Γ ⊢[PRAAx] RationalNormalForm.wellFormed b) (h : Γ ⊢[PRAAx] embed a ≐ embed b) : Γ ⊢[PRAAx] a ≐ b :=
  (RationalNormalForm.normalize_fixed_point a ha).eqSymm.eqTrans
    ((RationalGaussianEmbedding.scalar_recode_equal _ _ (RationalGaussianEmbedding.rational_equal_of_embed _ _ h)).eqTrans
      (RationalNormalForm.normalize_fixed_point b hb))

theorem zeros_evaluation (L z : PTm n) : Γ ⊢[PRAAx]
    RationalPolynomialGaussianEmbedding.evaluate (zeros L) z ≐ scalarZero :=
  canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    ((evaluation_transport _ _ L z (zeros_length L) (GaussianRationalPolynomialBuffers.zeros_length L)
      (zeros_embedded_entries L)).eqTrans
        ((GaussianRationalPolynomialBuffers.zeros_evaluation _ _).eqTrans RationalGaussianEmbedding.embed_zero.eqSymm))
theorem added_evaluation (C D L z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L) (hD : Γ ⊢[PRAAx] length D ≐ L) : Γ ⊢[PRAAx]
    RationalPolynomialGaussianEmbedding.evaluate (added C D L) z ≐
      RationalArithmetic.add (RationalPolynomialGaussianEmbedding.evaluate C z) (RationalPolynomialGaussianEmbedding.evaluate D z) := by
  apply canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.add_guard _ _)
  exact (evaluation_transport _ _ L z (added_length C D L) (GaussianRationalPolynomialBuffers.added_length _ _ _) (added_embedded_entries C D L)).eqTrans
    ((GaussianRationalPolynomialBuffers.added_evaluation _ _ _ _ (coefficients_length _ _) (coefficients_length _ _)).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (evaluation_at_width C L z hC).eqSymm
        (evaluation_at_width D L z hD).eqSymm).eqTrans (RationalGaussianEmbedding.embed_add _ _).eqSymm))
theorem scaled_evaluation (C s z : PTm n) : Γ ⊢[PRAAx]
    RationalPolynomialGaussianEmbedding.evaluate (scaled C s) z ≐
      RationalArithmetic.multiply s (RationalPolynomialGaussianEmbedding.evaluate C z) := by
  apply canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.multiply_guard _ _)
  exact (evaluation_transport _ _ (length C) z (scaled_length C s)
    ((GaussianRationalCoefficientScaling.scaled_length _ _).eqTrans (coefficients_length _ _)) (scaled_embedded_entries C s)).eqTrans
      ((GaussianRationalCoefficientScaling.evaluation_linearity _ _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
          (RationalPolynomialGaussianEmbedding.evaluation_conjugacy C z).eqSymm).eqTrans
            (RationalGaussianEmbedding.embed_multiply _ _).eqSymm))
theorem pad_evaluation (C t z : PTm n) : Γ ⊢[PRAAx]
    RationalPolynomialGaussianEmbedding.evaluate (leftPad C t) z ≐ RationalPolynomialGaussianEmbedding.evaluate C z := by
  apply canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
  exact (evaluation_transport _ _ (t+length C) z (pad_length C t)
    ((GaussianRationalPolynomialBuffers.pad_length _ _).eqTrans (congrAdd (.eqRefl _) (coefficients_length _ _))) (pad_embedded_entries C t)).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_evaluation _ _ _).eqTrans (RationalPolynomialGaussianEmbedding.evaluation_conjugacy C z).eqSymm)

def zerosF : PR 1 := PTm.toPR (zeros (var 0))
def addedF : PR 3 := PTm.toPR (added (var 0) (var 1) (var 2))
def scaledF : PR 2 := PTm.toPR (scaled (var 0) (var 1))
def paddedF : PR 3 := PTm.toPR (padded (var 0) (var 1) (var 2))
def leftPadF : PR 2 := PTm.toPR (leftPad (var 0) (var 1))
theorem zeros_at (L : PTm n) : Γ ⊢[PRAAx] ap1 zerosF L ≐ zeros L := by
  simpa [zerosF,ap1] using toPR_eq (Γ := Γ) (zeros (var 0) : PTm 1) ![L]
theorem added_at (C D L : PTm n) : Γ ⊢[PRAAx] ap3 addedF C D L ≐ added C D L := by
  simpa [addedF,ap3] using toPR_eq (Γ := Γ) (added (var 0) (var 1) (var 2) : PTm 3) ![C,D,L]
theorem scaled_at (C s : PTm n) : Γ ⊢[PRAAx] ap2 scaledF C s ≐ scaled C s := by
  simpa [scaledF,ap2] using toPR_eq (Γ := Γ) (scaled (var 0) (var 1) : PTm 2) ![C,s]
theorem padded_at (C L i : PTm n) : Γ ⊢[PRAAx] ap3 paddedF C L i ≐ padded C L i := by
  simpa [paddedF,ap3] using toPR_eq (Γ := Γ) (padded (var 0) (var 1) (var 2) : PTm 3) ![C,L,i]
theorem left_pad_at (C t : PTm n) : Γ ⊢[PRAAx] ap2 leftPadF C t ≐ leftPad C t := by
  simpa [leftPadF,ap2] using toPR_eq (Γ := Γ) (leftPad (var 0) (var 1) : PTm 2) ![C,t]

theorem program_added_embedding (C D L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) : Γ ⊢[PRAAx]
    embed (entry (ap3 addedF C D L) i) ≐
      entry (GaussianRationalPolynomialBuffers.added (coefficients C L) (coefficients D L) L) i :=
  (embed_congr (entry_congr (added_at C D L) (.eqRefl _))).eqTrans (added_embedding C D L i hi)
theorem program_scaled_embedding (C s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    embed (entry (ap2 scaledF C s) i) ≐ entry (GaussianRationalCoefficientScaling.scaled (coefficients C (length C)) (embed s)) i :=
  (embed_congr (entry_congr (scaled_at C s) (.eqRefl _))).eqTrans (scaled_embedding C s i hi)
theorem program_pad_embedding (C t i : PTm n) (hi : Γ ⊢[PRAAx] lt i (t+length C)) : Γ ⊢[PRAAx]
    embed (entry (ap2 leftPadF C t) i) ≐ entry (GaussianRationalPolynomialBuffers.leftPad (coefficients C (length C)) t) i :=
  (embed_congr (entry_congr (left_pad_at C t) (.eqRefl _))).eqTrans (pad_embedding C t i hi)

theorem actual_rational_zero_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ embed (entry (zeros (var 0)) (var 1)) ≐
      entry (GaussianRationalPolynomialBuffers.zeros (var 0)) (var 1)) := closeUniv 2 (.impI (zeros_embedding _ _ Prf.hyp0))
theorem actual_rational_padding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (embed (ap3 paddedF (var 0) (var 1) (var 2)) ≐
      GaussianRationalLinearProduct.padded (coefficients (var 0) (var 1)) (var 1) (var 2)) :=
  closeUniv 3 ((embed_congr (padded_at _ _ _)).eqTrans (padded_embedding _ _ _))
theorem actual_rational_added_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ embed (entry (ap3 addedF (var 0) (var 1) (var 2)) (var 3)) ≐
      entry (GaussianRationalPolynomialBuffers.added (coefficients (var 0) (var 2)) (coefficients (var 1) (var 2)) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (program_added_embedding _ _ _ _ Prf.hyp0))
theorem actual_rational_scaled_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (length (var 0)) ⟶ embed (entry (ap2 scaledF (var 0) (var 1)) (var 2)) ≐
      entry (GaussianRationalCoefficientScaling.scaled (coefficients (var 0) (length (var 0))) (embed (var 1))) (var 2)) :=
  closeUniv 3 (.impI (program_scaled_embedding _ _ _ Prf.hyp0))
theorem actual_rational_left_pad_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1+length (var 0)) ⟶ embed (entry (ap2 leftPadF (var 0) (var 1)) (var 2)) ≐
      entry (GaussianRationalPolynomialBuffers.leftPad (coefficients (var 0) (length (var 0))) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (program_pad_embedding _ _ _ Prf.hyp0))
theorem actual_rational_zero_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (RationalPolynomialGaussianEmbedding.evaluate (zeros (var 0)) (var 1) ≐ scalarZero) := closeUniv 2 (zeros_evaluation _ _)
theorem actual_rational_add_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ var 2 ⟶ length (var 1) ≐ var 2 ⟶
      RationalPolynomialGaussianEmbedding.evaluate (added (var 0) (var 1) (var 2)) (var 3) ≐ RationalArithmetic.add
        (RationalPolynomialGaussianEmbedding.evaluate (var 0) (var 3)) (RationalPolynomialGaussianEmbedding.evaluate (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (added_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_scale_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalPolynomialGaussianEmbedding.evaluate (scaled (var 0) (var 1)) (var 2) ≐
      RationalArithmetic.multiply (var 1) (RationalPolynomialGaussianEmbedding.evaluate (var 0) (var 2))) :=
  closeUniv 3 (scaled_evaluation _ _ _)
theorem actual_rational_pad_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalPolynomialGaussianEmbedding.evaluate (leftPad (var 0) (var 1)) (var 2) ≐
      RationalPolynomialGaussianEmbedding.evaluate (var 0) (var 2)) := closeUniv 3 (pad_evaluation _ _ _)
theorem actual_rational_buffer_lengths_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (zeros (var 2)) ≐ var 2 ⋏
      (length (added (var 0) (var 1) (var 2)) ≐ var 2 ⋏
        (length (scaled (var 0) (var 3)) ≐ length (var 0) ⋏
          length (leftPad (var 0) (var 4)) ≐ var 4+length (var 0)))) :=
  closeUniv 5 (.andI (zeros_length _) (.andI (added_length _ _ _) (.andI (scaled_length _ _) (pad_length _ _))))

end LeanProofs.IPRA.Analysis.RationalPolynomialBuffersGaussianEmbedding
