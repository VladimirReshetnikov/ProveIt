import IPRADerivations.Analysis.RationalPolynomialDeterminantTermsGaussianEmbedding
import IPRADerivations.Analysis.GaussianPolynomialDeterminant
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original rational polynomial determinant

The same retained numerical word scan drives original rational coefficient
addition of the actual signed product terms. Atomic QF prefix induction
derives every stored coefficient's literal Gaussian embedding. Evaluation
conjugacy follows from those coefficients, not from an input determinant law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero scalarOne)
open RationalPolynomialGaussianEmbedding (coefficients embed_congr)
open RationalPolynomialDeterminantTermsGaussianEmbedding (embeddedTable term)
open GaussianPolynomialDeterminant (wordCode data width)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def summand (M m L t : PTm n) : PTm n := term M m L (wordCode m t)
def initial : PTm 1 := RationalPolynomialBuffersGaussianEmbedding.zeros (width (fstT (sndT (var 0))) (sndT (sndT (var 0))))
def stepBody : PTm 3 := RationalPolynomialBuffersGaussianEmbedding.added (var 1)
  (summand (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0))
  (width (fstT (sndT (var 2))) (sndT (sndT (var 2))))
def prefixF : PR 2 := rec2 initial stepBody
def partialDeterminant (M m L t : PTm n) : PTm n := ap2 prefixF t (data M m L)
def determinant (M m L : PTm n) : PTm n := partialDeterminant M m L (Foundations.RuntimePermutationWords.count m)
@[simp] theorem subst_summand {l : ℕ} (σ : Fin n → PTm l) (M m L t : PTm n) :
    Syn.subst σ (summand M m L t) = summand (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ t) := by simp [summand]
@[simp] theorem subst_partialDeterminant {l : ℕ} (σ : Fin n → PTm l) (M m L t : PTm n) :
    Syn.subst σ (partialDeterminant M m L t) = partialDeterminant (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ t) := by simp [partialDeterminant]
@[simp] theorem subst_determinant {l : ℕ} (σ : Fin n → PTm l) (M m L : PTm n) :
    Syn.subst σ (determinant M m L) = determinant (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by simp [determinant]
theorem summand_congr {M M' m m' L L' t t' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hL : Γ ⊢[PRAAx] L ≐ L') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx] summand M m L t ≐ summand M' m' L' t' := by
  ipra_congr (summand (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hM, hm, hL, ht]
theorem partial_congr {M M' m m' L L' t t' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hL : Γ ⊢[PRAAx] L ≐ L') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    partialDeterminant M m L t ≐ partialDeterminant M' m' L' t' :=
  congrAp2 prefixF ht (congrPairT hM (congrPairT hm hL))
theorem added_congr {P P' Q Q' H H' : PTm n} (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hH : Γ ⊢[PRAAx] H ≐ H') : Γ ⊢[PRAAx]
    RationalPolynomialBuffersGaussianEmbedding.added P Q H ≐ RationalPolynomialBuffersGaussianEmbedding.added P' Q' H' :=
  (RationalPolynomialBuffersGaussianEmbedding.added_at _ _ _).eqSymm.eqTrans
    ((congrAp3 RationalPolynomialBuffersGaussianEmbedding.addedF hP hQ hH).eqTrans (RationalPolynomialBuffersGaussianEmbedding.added_at _ _ _))
theorem prefix_zero (M m L : PTm n) : Γ ⊢[PRAAx] partialDeterminant M m L zero ≐ RationalPolynomialBuffersGaussianEmbedding.zeros (width m L) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data M m L)
  simp only [initial,RationalPolynomialBuffersGaussianEmbedding.subst_zeros,GaussianPolynomialDeterminant.subst_width,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero] at e
  have tail := snd_pair (Γ := Γ) M (pairT m L)
  have hWidth := congrSucc (congrMul ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _)))
  exact e.eqTrans ((RationalPolynomialBuffersGaussianEmbedding.zeros_at _).eqSymm.eqTrans
    ((congrAp1 RationalPolynomialBuffersGaussianEmbedding.zerosF hWidth).eqTrans (RationalPolynomialBuffersGaussianEmbedding.zeros_at _)))
theorem prefix_succ (M m L t : PTm n) : Γ ⊢[PRAAx] partialDeterminant M m L (succ t) ≐
    RationalPolynomialBuffersGaussianEmbedding.added (partialDeterminant M m L t) (summand M m L t) (width m L) := by
  have e := rec2_succ (Γ := Γ) initial stepBody t (data M m L)
  simp only [stepBody,RationalPolynomialBuffersGaussianEmbedding.subst_added,subst_summand,GaussianPolynomialDeterminant.subst_width,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  have tail := snd_pair (Γ := Γ) M (pairT m L)
  exact e.eqTrans (added_congr (.eqRefl _) (summand_congr (fst_pair _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd tail).eqTrans (snd_pair _ _)) (.eqRefl _))
      (congrSucc (congrMul ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _)))))
theorem prefix_length (M m L t : PTm n) : Γ ⊢[PRAAx] length (partialDeterminant M m L t) ≐ width m L := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_zero _ _ _))).eqTrans
      (RationalPolynomialBuffersGaussianEmbedding.zeros_length _)
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_succ _ _ _ _))).eqTrans
      (RationalPolynomialBuffersGaussianEmbedding.added_length _ _ _)

def coefficientLaw (M m L s t : PTm n) : Fm PTm n := embed (entry (partialDeterminant M m L t) s) ≐
  entry (GaussianPolynomialDeterminant.partialDeterminant (embeddedTable M m L) m L t) s
@[simp] theorem subst_coefficientLaw {l : ℕ} (σ : Fin n → PTm l) (M m L s t : PTm n) :
    (coefficientLaw M m L s t).subst σ = coefficientLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ s) (Syn.subst σ t) := by
  simp [coefficientLaw]
theorem coefficient_base (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx] coefficientLaw M m L s zero :=
  (embed_congr (entry_congr (prefix_zero M m L) (.eqRefl s))).eqTrans
    ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ s ((succ_monus_succ _ _).eqTrans hs)).eqTrans
      (entry_congr (GaussianPolynomialDeterminant.prefix_zero (embeddedTable M m L) m L).eqSymm (.eqRefl _)))
theorem coefficient_step (M m L s t : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L))
    (ih : Γ ⊢[PRAAx] coefficientLaw M m L s t) : Γ ⊢[PRAAx] coefficientLaw M m L s (succ t) := by
  have original := (embed_congr ((entry_congr (prefix_succ M m L t) (.eqRefl s)).eqTrans
    (RationalPolynomialBuffersGaussianEmbedding.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)))).eqTrans
      (RationalGaussianEmbedding.embed_add _ _)
  have moved := GaussianRationalSyntheticDivision.qadd_congr ih
    (RationalPolynomialDeterminantTermsGaussianEmbedding.term_entry_embedding M m L (wordCode m t) s hs)
  have gaussian := (entry_congr (GaussianPolynomialDeterminant.prefix_succ (embeddedTable M m L) m L t) (.eqRefl s)).eqTrans
    (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))
  exact original.eqTrans (moved.eqTrans gaussian.eqSymm)
theorem prefix_coefficient_embedding (M m L s t : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx] coefficientLaw M m L s t := by
  have hss : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift m*Syn.shift L) := by
    simpa only [Fm.shift,subst_le,PTm.subst_mul,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (coefficientLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift s) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact coefficient_base M m L s hs
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact coefficient_step _ _ _ _ _ hss.wk Prf.hyp0
  simpa only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem determinant_length (M m L : PTm n) : Γ ⊢[PRAAx] length (determinant M m L) ≐ width m L := prefix_length _ _ _ _
theorem coefficient_embedding (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    embed (entry (determinant M m L) s) ≐ entry (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) s :=
  prefix_coefficient_embedding M m L s _ hs
theorem determinant_entries (M m L : PTm n) : Γ ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries
    (determinant M m L) (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) (width m L) := by
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (Syn.shift m*Syn.shift L)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (Syn.shift m*Syn.shift L) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_determinant,RationalPolynomialDeterminantTermsGaussianEmbedding.subst_embeddedTable,
    GaussianPolynomialDeterminant.subst_determinant,GaussianPolynomialDeterminant.subst_width,GaussianPolynomialDeterminant.width,
    ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using coefficient_embedding (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) bound
theorem evaluation_conjugacy (M m L z : PTm n) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate (determinant M m L) z) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) (embed z) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ (width m L) z (determinant_length _ _ _)
    (GaussianPolynomialDeterminant.determinant_length _ _ _) (determinant_entries _ _ _)

theorem prefix_coefficient_well_formed (M m L s t : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (partialDeterminant M m L t) s) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact RationalArithmetic.guard_congr
      ((entry_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_zero _ _ _)) (.eqRefl s)).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs.wk)))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · exact RationalArithmetic.guard_congr
      ((entry_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_succ _ _ _ _)) (.eqRefl s)).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs.wk))) (RationalArithmetic.add_guard _ _)
theorem determinant_coefficient_well_formed (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (determinant M m L) s) := prefix_coefficient_well_formed _ _ _ _ _ hs
theorem coefficient_zero_iff (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx] Fm.iff
    (RationalArgmin.rationalEq (entry (determinant M m L) s) scalarZero)
    (entry (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) s ≐ GaussianRationalHorner.qzero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (coefficient_embedding M m L s hs.wk).eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff _).iffMpr Prf.hyp0)
  · exact (RationalGaussianEmbedding.zero_iff _).iffMp ((coefficient_embedding M m L s hs.wk).eqTrans Prf.hyp0)
theorem evaluation_zero_iff (M m L z : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (RationalArgmin.rationalEq (RationalPolynomialGaussianEmbedding.evaluate (determinant M m L) z) scalarZero)
    (GaussianRationalHorner.evaluate (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) (embed z) ≐ GaussianRationalHorner.qzero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (evaluation_conjugacy M m L z).eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff _).iffMpr Prf.hyp0)
  · exact (RationalGaussianEmbedding.zero_iff _).iffMp ((evaluation_conjugacy M m L z).eqTrans Prf.hyp0)
theorem empty_evaluation (M L z : PTm n) : Γ ⊢[PRAAx] RationalPolynomialGaussianEmbedding.evaluate (determinant M zero L) z ≐ scalarOne :=
  RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) ((evaluation_conjugacy M zero L z).eqTrans
      ((GaussianPolynomialDeterminant.empty_evaluation _ _ _).eqTrans RationalGaussianEmbedding.embed_one.eqSymm))

def determinantF : PR 3 := PTm.toPR (determinant (var 0) (var 1) (var 2))
def output (M m L t : PTm n) : PTm n := pairT (partialDeterminant M m L t) (pairT (determinant M m L) (embeddedTable M m L))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (M m L t : PTm n) : PTm n := PTm.app outputF ![M,m,L,t]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L t : PTm n) :
    Syn.subst σ (output M m L t) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ t) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L t : PTm n) :
    Syn.subst σ (run M m L t) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ t) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem determinant_at (M m L : PTm n) : Γ ⊢[PRAAx] ap3 determinantF M m L ≐ determinant M m L := by
  simpa [determinantF,ap3] using toPR_eq (Γ := Γ) (determinant (var 0) (var 1) (var 2) : PTm 3) ![M,m,L]
theorem program_at (M m L t : PTm n) : Γ ⊢[PRAAx] run M m L t ≐ output M m L t := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![M,m,L,t]
theorem returned_prefix (M m L t : PTm n) : Γ ⊢[PRAAx] fstT (run M m L t) ≐ partialDeterminant M m L t :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_determinant (M m L t : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run M m L t)) ≐ determinant M m L :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_table (M m L t : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run M m L t)) ≐ embeddedTable M m L :=
  (congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_coefficient (M m L t s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    embed (entry (fstT (sndT (run M m L t))) s) ≐ entry (GaussianPolynomialDeterminant.determinant (embeddedTable M m L) m L) s :=
  (embed_congr (entry_congr (returned_determinant M m L t) (.eqRefl s))).eqTrans (coefficient_embedding M m L s hs)

theorem actual_rational_determinant_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (partialDeterminant (var 0) (var 1) (var 2) (succ (var 3)) ≐ RationalPolynomialBuffersGaussianEmbedding.added
      (partialDeterminant (var 0) (var 1) (var 2) (var 3)) (summand (var 0) (var 1) (var 2) (var 3)) (width (var 1) (var 2))) :=
  closeUniv 4 (prefix_succ _ _ _ _)
theorem actual_rational_polynomial_determinant_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (ap3 determinantF (var 0) (var 1) (var 2)) ≐ width (var 1) (var 2)) :=
  closeUniv 3 ((congrFst (determinant_at _ _ _)).eqTrans (determinant_length _ _ _))
theorem actual_rational_determinant_prefix_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1*var 2) ⟶ embed (entry (partialDeterminant (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐
      entry (GaussianPolynomialDeterminant.partialDeterminant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (prefix_coefficient_embedding _ _ _ _ _ Prf.hyp0))
theorem actual_rational_polynomial_determinant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1*var 2) ⟶ embed (entry (determinant (var 0) (var 1) (var 2)) (var 3)) ≐
      entry (GaussianPolynomialDeterminant.determinant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (coefficient_embedding _ _ _ _ Prf.hyp0))
theorem actual_rational_polynomial_determinant_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (embed (RationalPolynomialGaussianEmbedding.evaluate (determinant (var 0) (var 1) (var 2)) (var 3)) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialDeterminant.determinant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) (embed (var 3))) :=
  closeUniv 4 (evaluation_conjugacy _ _ _ _)
theorem actual_rational_determinant_coefficient_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1*var 2) ⟶ Fm.iff (RationalArgmin.rationalEq (entry (determinant (var 0) (var 1) (var 2)) (var 3)) scalarZero)
      (entry (GaussianPolynomialDeterminant.determinant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) (var 3) ≐ GaussianRationalHorner.qzero)) :=
  closeUniv 4 (.impI (coefficient_zero_iff _ _ _ _ Prf.hyp0))
theorem actual_rational_determinant_evaluation_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (RationalArgmin.rationalEq (RationalPolynomialGaussianEmbedding.evaluate (determinant (var 0) (var 1) (var 2)) (var 3)) scalarZero)
      (GaussianRationalHorner.evaluate (GaussianPolynomialDeterminant.determinant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) (embed (var 3)) ≐ GaussianRationalHorner.qzero)) :=
  closeUniv 4 (evaluation_zero_iff _ _ _ _)
theorem actual_rational_determinant_empty_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalPolynomialGaussianEmbedding.evaluate (determinant (var 0) zero (var 1)) (var 2) ≐ scalarOne) := closeUniv 3 (empty_evaluation _ _ _)
theorem actual_rational_determinant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_rational_returned_determinant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1*var 2) ⟶ embed (entry (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (var 4)) ≐
      entry (GaussianPolynomialDeterminant.determinant (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) (var 4)) :=
  closeUniv 5 (.impI (returned_coefficient _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantGaussianEmbedding
