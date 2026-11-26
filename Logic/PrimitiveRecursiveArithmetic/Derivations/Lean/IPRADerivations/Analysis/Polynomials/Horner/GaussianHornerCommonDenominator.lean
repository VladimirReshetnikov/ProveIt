import IPRADerivations.Analysis.Geometry.Distances.GaussianRelativeNormTriangle
import IPRADerivations.Analysis.Polynomials.Horner.GaussianReciprocalHorner
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalNormalization
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual Horner-at-one sums at one computed common denominator

A genuine QF prefix induction connects the actual rational Horner
program at one to the actual Gaussian-integer finite fold. The generic
helper accepts representations only of individual original coefficients,
never a sum or prefix identity. The concrete source and target endpoints
derive every representation and denominator from their actual joint
normalization pool. Empty lists and raw noncanonical input codes are
included. Only the fixed term-evaluator schema is external; all lists,
denominators, lengths, prefix counters and persistent data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianHornerCommonDenominator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd horner evaluate represents subst_represents hornerF canonical ofGaussian)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qadd_congr)
open LeanProofs.IPRA.Analysis.GaussianRelativeNormTriangle
  (gaussianSum gaussianSumF subst_gaussianSum gaussian_sum_zero gaussian_sum_succ)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (zeroCode add scale)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_code equal_refl equal_of_values equal_re equal_im re_add im_add re_scale im_scale re_zero im_zero)
open LeanProofs.IPRA.Analysis.GaussianRationalNormalization
  (commonD sourceNumerators targetNumerators commonD_positive source_clearing target_clearing)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def entryF : PR 2 := PTm.toPR (entry (var 1) (var 0))
def integerSum (G m : PTm n) : PTm n := gaussianSum entryF m G
def rationalSum (Q : PTm n) : PTm n := evaluate Q qone

@[simp] theorem subst_integerSum {l : ℕ} (σ : Fin n → PTm l) (G m : PTm n) :
    Syn.subst σ (integerSum G m) = integerSum (Syn.subst σ G) (Syn.subst σ m) := by simp [integerSum]
@[simp] theorem subst_rationalSum {l : ℕ} (σ : Fin n → PTm l) (Q : PTm n) :
    Syn.subst σ (rationalSum Q) = rationalSum (Syn.subst σ Q) := by simp [rationalSum]

theorem entry_program (G i : PTm n) : Γ ⊢[PRAAx] ap2 entryF i G ≐ entry G i := by
  simpa [entryF,ap2] using toPR_eq (Γ := Γ) (entry (var 1) (var 0) : PTm 2) ![i,G]

theorem integer_sum_zero (G : PTm n) : Γ ⊢[PRAAx] integerSum G zero ≐ zeroCode := gaussian_sum_zero _ _

theorem add_code_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] add a b ≐ add a' b' := by
  ipra_congr (add (var 0) (var 1) : PTm 2) with [ha, hb]

theorem integer_sum_succ (G m : PTm n) : Γ ⊢[PRAAx]
    integerSum G (succ m) ≐ add (integerSum G m) (entry G m) :=
  (gaussian_sum_succ entryF m G).eqTrans (add_code_congr (.eqRefl _) (entry_program G m))

def entryRepresentations (f : PR 2) (Q D m x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ represents (entry (Syn.shift Q) (var 0))
    (ap2 f (var 0) (Syn.shift x)) (Syn.shift D))

@[simp] theorem subst_entryRepresentations (f : PR 2) {l : ℕ} (σ : Fin n → PTm l) (Q D m x : PTm n) :
    (entryRepresentations f Q D m x).subst σ = entryRepresentations f (Syn.subst σ Q) (Syn.subst σ D)
      (Syn.subst σ m) (Syn.subst σ x) := by simp [entryRepresentations,Syn.subst_shift,Syn.shift_subst]

theorem entry_representation_at (f : PR 2) (Q D m x i : PTm n)
    (h : Γ ⊢[PRAAx] entryRepresentations f Q D m x) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    represents (entry Q i) (ap2 f i x) D := by
  have rule : Γ ⊢[PRAAx] lt i m ⟶ represents (entry Q i) (ap2 f i x) D := by
    simpa [entryRepresentations] using h.allE i
  exact .impE rule hi

def prefixLaw (f : PR 2) (Q D m x k : PTm n) : Fm PTm n := le k m ⟶
  represents (horner Q qone k) (gaussianSum f k x) D

@[simp] theorem subst_prefixLaw (f : PR 2) {l : ℕ} (σ : Fin n → PTm l) (Q D m x k : PTm n) :
    (prefixLaw f Q D m x k).subst σ = prefixLaw f (Syn.subst σ Q) (Syn.subst σ D)
      (Syn.subst σ m) (Syn.subst σ x) (Syn.subst σ k) := by simp [prefixLaw]

theorem prefix_zero (f : PR 2) (Q D x : PTm n) : Γ ⊢[PRAAx]
    represents (horner Q qone zero) (gaussianSum f zero x) D :=
  GaussianRationalHorner.represents_congr (GaussianRationalHorner.horner_zero Q qone).eqSymm
    (equal_of_code (gaussian_sum_zero f x).eqSymm) (.eqRefl _) (GaussianRationalHorner.zero_represents D)

theorem prefix_step (f : PR 2) (Q D m x k : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hEntries : Γ ⊢[PRAAx] entryRepresentations f Q D m x)
    (hk : Γ ⊢[PRAAx] lt k m)
    (hIH : Γ ⊢[PRAAx] represents (horner Q qone k) (gaussianSum f k x) D) : Γ ⊢[PRAAx]
    represents (horner Q qone (succ k)) (gaussianSum f (succ k) x) D := by
  have code : Γ ⊢[PRAAx] horner Q qone (succ k) ≐ qadd (horner Q qone k) (entry Q k) :=
    (GaussianRationalHorner.horner_succ Q qone k).eqTrans
      (qadd_congr (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)) (.eqRefl _))
  exact GaussianRationalHorner.represents_congr code.eqSymm
    (equal_of_code (gaussian_sum_succ f k x).eqSymm) (.eqRefl _)
      (GaussianRationalHorner.qadd_represents _ _ _ _ _ hD hIH
        (entry_representation_at f Q D m x k hEntries hk))

/-- Genuine QF prefix clearing for an arbitrary fixed actual term program.
The only representation premise concerns individual original entries. -/
theorem prefix_represents (f : PR 2) (Q D m x k : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hEntries : Γ ⊢[PRAAx] entryRepresentations f Q D m x)
    (hk : Γ ⊢[PRAAx] le k m) : Γ ⊢[PRAAx]
    represents (horner Q qone k) (gaussianSum f k x) D := by
  have dShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hD.shift
  have eShift : Γ.map Fm.shift ⊢[PRAAx]
      entryRepresentations f (Syn.shift Q) (Syn.shift D) (Syn.shift m) (Syn.shift x) := by
    simpa only [Fm.shift,subst_entryRepresentations,Syn.shift] using hEntries.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f (Syn.shift Q) (Syn.shift D) (Syn.shift m) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero f Q D x)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_step _ _ _ _ _ _ dShift.wk.wk eShift.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw f Q D m x k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem horner_clearing (f : PR 2) (Q D m x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hEntries : Γ ⊢[PRAAx] entryRepresentations f Q D m x) : Γ ⊢[PRAAx]
    represents (horner Q qone m) (gaussianSum f m x) D :=
  prefix_represents f Q D m x m hD hEntries (le_refl _)

theorem evaluate_represents (f : PR 2) (Q D x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hEntries : Γ ⊢[PRAAx] entryRepresentations f Q D (length Q) x) : Γ ⊢[PRAAx]
    represents (rationalSum Q) (gaussianSum f (length Q) x) D :=
  horner_clearing f Q D (length Q) x hD hEntries

theorem source_entry_representations (S T ref : PTm n) : Γ ⊢[PRAAx]
    entryRepresentations entryF S (commonD S T ref) (length S) (sourceNumerators S T ref) := by
  refine .allI (.impI ?_)
  have h : lt (var 0) (length (Syn.shift S)) :: Γ.map Fm.shift ⊢[PRAAx]
      represents (entry (Syn.shift S) (var 0))
        (ap2 entryF (var 0) (sourceNumerators (Syn.shift S) (Syn.shift T) (Syn.shift ref)))
        (commonD (Syn.shift S) (Syn.shift T) (Syn.shift ref)) :=
    GaussianRationalHorner.represents_congr (.eqRefl _)
      (equal_of_code (entry_program _ _).eqSymm) (.eqRefl _)
        (source_clearing (Syn.shift S) (Syn.shift T) (Syn.shift ref) (var 0) Prf.hyp0)
  simpa only [Syn.shift,subst_length,GaussianRationalNormalization.subst_commonD,
    GaussianRationalNormalization.subst_sourceNumerators] using h

theorem target_entry_representations (S T ref : PTm n) : Γ ⊢[PRAAx]
    entryRepresentations entryF T (commonD S T ref) (length T) (targetNumerators S T ref) := by
  refine .allI (.impI ?_)
  have h : lt (var 0) (length (Syn.shift T)) :: Γ.map Fm.shift ⊢[PRAAx]
      represents (entry (Syn.shift T) (var 0))
        (ap2 entryF (var 0) (targetNumerators (Syn.shift S) (Syn.shift T) (Syn.shift ref)))
        (commonD (Syn.shift S) (Syn.shift T) (Syn.shift ref)) :=
    GaussianRationalHorner.represents_congr (.eqRefl _)
      (equal_of_code (entry_program _ _).eqSymm) (.eqRefl _)
        (target_clearing (Syn.shift S) (Syn.shift T) (Syn.shift ref) (var 0) Prf.hyp0)
  simpa only [Syn.shift,subst_length,GaussianRationalNormalization.subst_commonD,
    GaussianRationalNormalization.subst_targetNumerators] using h

/-- Both concrete sums use the same denominator computed from the two
original lists and reference. There is no common-denominator input premise. -/
theorem source_sum_represents (S T ref : PTm n) : Γ ⊢[PRAAx]
    represents (rationalSum S) (integerSum (sourceNumerators S T ref) (length S)) (commonD S T ref) :=
  evaluate_represents entryF S _ _ (commonD_positive S T ref) (source_entry_representations S T ref)

theorem target_sum_represents (S T ref : PTm n) : Γ ⊢[PRAAx]
    represents (rationalSum T) (integerSum (targetNumerators S T ref) (length T)) (commonD S T ref) :=
  evaluate_represents entryF T _ _ (commonD_positive S T ref) (target_entry_representations S T ref)

/-! Actual integer finite folds respect coefficientwise scale and addition.
These equalities concern decoded signed Gaussian values, as required by
the norm kernel; redundant signed-pair codes are not falsely identified. -/
def scaledEntryBody : PTm 2 := scale (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def scaledEntryF : PR 2 := PTm.toPR scaledEntryBody
def scaledSum (B G m : PTm n) : PTm n := gaussianSum scaledEntryF m (pairT B G)
def addedEntryBody : PTm 2 := add (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))
def addedEntryF : PR 2 := PTm.toPR addedEntryBody
def addedSum (G H m : PTm n) : PTm n := gaussianSum addedEntryF m (pairT G H)

@[simp] theorem subst_scaledSum {l : ℕ} (σ : Fin n → PTm l) (B G m : PTm n) :
    Syn.subst σ (scaledSum B G m) = scaledSum (Syn.subst σ B) (Syn.subst σ G) (Syn.subst σ m) := by simp [scaledSum]
@[simp] theorem subst_addedSum {l : ℕ} (σ : Fin n → PTm l) (G H m : PTm n) :
    Syn.subst σ (addedSum G H m) = addedSum (Syn.subst σ G) (Syn.subst σ H) (Syn.subst σ m) := by simp [addedSum]

theorem scale_code_congr {B B' a a' : PTm n} (hB : Γ ⊢[PRAAx] B ≐ B') (ha : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] scale B a ≐ scale B' a' := by
  ipra_congr (scale (var 0) (var 1) : PTm 2) with [hB, ha]

theorem scaled_entry_at (B G i : PTm n) : Γ ⊢[PRAAx]
    ap2 scaledEntryF i (pairT B G) ≐ scale B (entry G i) := by
  have h := toPR_eq (Γ := Γ) scaledEntryBody ![i,pairT B G]
  simp only [scaledEntryBody,ComplexLogarithmRemainder.subst_scale,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  exact h.eqTrans (scale_code_congr (fst_pair _ _)
    (Foundations.SequenceComposition.entry_congr (snd_pair _ _) (.eqRefl _)))

theorem added_entry_at (G H i : PTm n) : Γ ⊢[PRAAx]
    ap2 addedEntryF i (pairT G H) ≐ add (entry G i) (entry H i) := by
  have h := toPR_eq (Γ := Γ) addedEntryBody ![i,pairT G H]
  simp only [addedEntryBody,ComplexLogarithmRemainder.subst_add,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  exact h.eqTrans (add_code_congr (Foundations.SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _))
    (Foundations.SequenceComposition.entry_congr (snd_pair _ _) (.eqRefl _)))

theorem scaled_sum_succ (B G m : PTm n) : Γ ⊢[PRAAx]
    scaledSum B G (succ m) ≐ add (scaledSum B G m) (scale B (entry G m)) :=
  (gaussian_sum_succ scaledEntryF m (pairT B G)).eqTrans (add_code_congr (.eqRefl _) (scaled_entry_at B G m))

theorem added_sum_succ (G H m : PTm n) : Γ ⊢[PRAAx]
    addedSum G H (succ m) ≐ add (addedSum G H m) (add (entry G m) (entry H m)) :=
  (gaussian_sum_succ addedEntryF m (pairT G H)).eqTrans (add_code_congr (.eqRefl _) (added_entry_at G H m))

theorem sum_scale_zero (B G : PTm n) : Γ ⊢[PRAAx] equal (scaledSum B G zero) (scale B (integerSum G zero)) := by
  have hs := GaussianRootAlgebra.values_of_code (gaussian_sum_zero (Γ := Γ) scaledEntryF (pairT B G))
  have hi := GaussianRootAlgebra.values_of_code (integer_sum_zero (Γ := Γ) G)
  apply equal_of_values
  · simp only [scaledSum,re_scale]; rw [hs.1,hi.1,re_zero]; ring
  · simp only [scaledSum,im_scale]; rw [hs.2,hi.2,im_zero]; ring

theorem sum_scale_step (B G m : PTm n)
    (hIH : Γ ⊢[PRAAx] equal (scaledSum B G m) (scale B (integerSum G m))) : Γ ⊢[PRAAx]
    equal (scaledSum B G (succ m)) (scale B (integerSum G (succ m))) := by
  have hs := GaussianRootAlgebra.values_of_code (scaled_sum_succ (Γ := Γ) B G m)
  have hi := GaussianRootAlgebra.values_of_code (integer_sum_succ (Γ := Γ) G m)
  apply equal_of_values
  · rw [hs.1]; simp only [re_add,re_scale]; rw [equal_re hIH,hi.1]; simp only [re_add,re_scale]; ring
  · rw [hs.2]; simp only [im_add,im_scale]; rw [equal_im hIH,hi.2]; simp only [im_add,im_scale]; ring

theorem integer_sum_scale (B G m : PTm n) : Γ ⊢[PRAAx]
    equal (scaledSum B G m) (scale B (integerSum G m)) := by
  have all : Γ ⊢[PRAAx] .all (equal (scaledSum (Syn.shift B) (Syn.shift G) (var 0))
      (scale (Syn.shift B) (integerSum (Syn.shift G) (var 0)))) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [GaussianRootAlgebra.subst_equal,subst_scaledSum,ComplexLogarithmRemainder.subst_scale,
        subst_integerSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact sum_scale_zero B G
    · simp only [GaussianRootAlgebra.subst_equal,subst_scaledSum,ComplexLogarithmRemainder.subst_scale,
        subst_integerSum,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact sum_scale_step _ _ _ Prf.hyp0
  simpa only [GaussianRootAlgebra.subst_equal,subst_scaledSum,ComplexLogarithmRemainder.subst_scale,
    subst_integerSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

theorem sum_add_zero (G H : PTm n) : Γ ⊢[PRAAx]
    equal (addedSum G H zero) (add (integerSum G zero) (integerSum H zero)) := by
  have hs := GaussianRootAlgebra.values_of_code (gaussian_sum_zero (Γ := Γ) addedEntryF (pairT G H))
  have hg := GaussianRootAlgebra.values_of_code (integer_sum_zero (Γ := Γ) G)
  have hh := GaussianRootAlgebra.values_of_code (integer_sum_zero (Γ := Γ) H)
  apply equal_of_values
  · simp only [addedSum,re_add]; rw [hs.1,hg.1,hh.1,re_zero]; ring
  · simp only [addedSum,im_add]; rw [hs.2,hg.2,hh.2,im_zero]; ring

theorem sum_add_step (G H m : PTm n)
    (hIH : Γ ⊢[PRAAx] equal (addedSum G H m) (add (integerSum G m) (integerSum H m))) : Γ ⊢[PRAAx]
    equal (addedSum G H (succ m)) (add (integerSum G (succ m)) (integerSum H (succ m))) := by
  have hs := GaussianRootAlgebra.values_of_code (added_sum_succ (Γ := Γ) G H m)
  have hg := GaussianRootAlgebra.values_of_code (integer_sum_succ (Γ := Γ) G m)
  have hh := GaussianRootAlgebra.values_of_code (integer_sum_succ (Γ := Γ) H m)
  apply equal_of_values
  · rw [hs.1]; simp only [re_add]; rw [equal_re hIH,hg.1,hh.1]; simp only [re_add]; ring
  · rw [hs.2]; simp only [im_add]; rw [equal_im hIH,hg.2,hh.2]; simp only [im_add]; ring

theorem integer_sum_add (G H m : PTm n) : Γ ⊢[PRAAx]
    equal (addedSum G H m) (add (integerSum G m) (integerSum H m)) := by
  have all : Γ ⊢[PRAAx] .all (equal (addedSum (Syn.shift G) (Syn.shift H) (var 0))
      (add (integerSum (Syn.shift G) (var 0)) (integerSum (Syn.shift H) (var 0)))) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [GaussianRootAlgebra.subst_equal,subst_addedSum,ComplexLogarithmRemainder.subst_add,
        subst_integerSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact sum_add_zero G H
    · simp only [GaussianRootAlgebra.subst_equal,subst_addedSum,ComplexLogarithmRemainder.subst_add,
        subst_integerSum,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact sum_add_step _ _ _ Prf.hyp0
  simpa only [GaussianRootAlgebra.subst_equal,subst_addedSum,ComplexLogarithmRemainder.subst_add,
    subst_integerSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

/-- Canonical actual evaluations have the literal normalized common-D
code, without any canonical-storage condition on the input coefficients. -/
theorem evaluate_exact (f : PR 2) (Q D x : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hEntries : Γ ⊢[PRAAx] entryRepresentations f Q D (length Q) x) : Γ ⊢[PRAAx]
    rationalSum Q ≐ ofGaussian (gaussianSum f (length Q) x) D :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.horner_canonical _ _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD) hD
    (evaluate_represents f Q D x hD hEntries) (GaussianRationalHorner.ofGaussian_represents _ _ hD)

theorem source_sum_exact (S T ref : PTm n) : Γ ⊢[PRAAx]
    rationalSum S ≐ ofGaussian (integerSum (sourceNumerators S T ref) (length S)) (commonD S T ref) :=
  evaluate_exact entryF _ _ _ (commonD_positive S T ref) (source_entry_representations S T ref)

theorem target_sum_exact (S T ref : PTm n) : Γ ⊢[PRAAx]
    rationalSum T ≐ ofGaussian (integerSum (targetNumerators S T ref) (length T)) (commonD S T ref) :=
  evaluate_exact entryF _ _ _ (commonD_positive S T ref) (target_entry_representations S T ref)

theorem joint_sum_represents (S T ref : PTm n) : Γ ⊢[PRAAx]
    represents (qadd (rationalSum S) (rationalSum T))
      (add (integerSum (sourceNumerators S T ref) (length S))
        (integerSum (targetNumerators S T ref) (length T))) (commonD S T ref) :=
  GaussianRationalHorner.qadd_represents _ _ _ _ _ (commonD_positive S T ref)
    (source_sum_represents S T ref) (target_sum_represents S T ref)

/-! Fixed actual sum programs and literal pool output metadata. -/
def integerSumF : PR 2 := gaussianSumF entryF
def rationalSumF : PR 1 := PTm.toPR (rationalSum (var 0))
def output (S T ref : PTm n) : PTm n := pairT (commonD S T ref)
  (pairT (rationalSum S) (pairT (rationalSum T)
    (pairT (integerSum (sourceNumerators S T ref) (length S))
      (integerSum (targetNumerators S T ref) (length T)))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (S T ref : PTm n) : PTm n := ap3 outputF S T ref

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (S T ref : PTm n) :
    Syn.subst σ (output S T ref) = output (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (S T ref : PTm n) :
    Syn.subst σ (run S T ref) = run (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [run]

theorem integer_sum_program (G m : PTm n) : Γ ⊢[PRAAx] ap2 integerSumF m G ≐ integerSum G m := .eqRefl _
theorem rational_sum_program (Q : PTm n) : Γ ⊢[PRAAx] ap1 rationalSumF Q ≐ rationalSum Q := by
  simpa [rationalSumF,ap1] using toPR_eq (Γ := Γ) (rationalSum (var 0) : PTm 1) ![Q]
theorem program_at (S T ref : PTm n) : Γ ⊢[PRAAx] run S T ref ≐ output S T ref := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![S,T,ref]

theorem returned_denominator (S T ref : PTm n) : Γ ⊢[PRAAx] fstT (run S T ref) ≐ commonD S T ref :=
  (congrFst (program_at S T ref)).eqTrans (fst_pair _ _)
theorem returned_source (S T ref : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run S T ref)) ≐ rationalSum S :=
  (congrFst ((congrSnd (program_at S T ref)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_target (S T ref : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run S T ref))) ≐ rationalSum T :=
  (congrFst ((congrSnd ((congrSnd (program_at S T ref)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_source_integer (S T ref : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run S T ref)))) ≐ integerSum (sourceNumerators S T ref) (length S) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at S T ref)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_target_integer (S T ref : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run S T ref)))) ≐ integerSum (targetNumerators S T ref) (length T) :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at S T ref)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_source_represents (S T ref : PTm n) : Γ ⊢[PRAAx]
    represents (fstT (sndT (run S T ref))) (fstT (sndT (sndT (sndT (run S T ref))))) (fstT (run S T ref)) :=
  GaussianRationalHorner.represents_congr (returned_source S T ref).eqSymm
    (equal_of_code (returned_source_integer S T ref).eqSymm) (returned_denominator S T ref).eqSymm
    (source_sum_represents S T ref)
theorem returned_target_represents (S T ref : PTm n) : Γ ⊢[PRAAx]
    represents (fstT (sndT (sndT (run S T ref)))) (sndT (sndT (sndT (sndT (run S T ref))))) (fstT (run S T ref)) :=
  GaussianRationalHorner.represents_congr (returned_target S T ref).eqSymm
    (equal_of_code (returned_target_integer S T ref).eqSymm) (returned_denominator S T ref).eqSymm
    (target_sum_represents S T ref)

theorem horner_prefix_clearing_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ entryRepresentations f (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 2) ⟶
      represents (horner (var 0) qone (var 4)) (gaussianSum f (var 4) (var 3)) (var 1)) :=
  closeUniv 5 (.impI (.impI (.impI (prefix_represents f _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem horner_clearing_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ entryRepresentations f (var 0) (var 1) (var 2) (var 3) ⟶
      represents (horner (var 0) qone (var 2)) (gaussianSum f (var 2) (var 3)) (var 1)) :=
  closeUniv 4 (.impI (.impI (horner_clearing f _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem evaluate_clearing_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ entryRepresentations f (var 0) (var 1) (length (var 0)) (var 2) ⟶
      represents (rationalSum (var 0)) (gaussianSum f (length (var 0)) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (evaluate_represents f _ _ _ Prf.hyp1 Prf.hyp0)))

theorem normalized_sums_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (commonD (var 0) (var 1) (var 2)) ⋏
      (represents (rationalSum (var 0)) (integerSum (sourceNumerators (var 0) (var 1) (var 2)) (length (var 0)))
        (commonD (var 0) (var 1) (var 2)) ⋏
       represents (rationalSum (var 1)) (integerSum (targetNumerators (var 0) (var 1) (var 2)) (length (var 1)))
        (commonD (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (commonD_positive _ _ _) (.andI (source_sum_represents _ _ _) (target_sum_represents _ _ _)))

theorem integer_sum_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (scaledSum (var 0) (var 1) (var 2)) (scale (var 0) (integerSum (var 1) (var 2)))) :=
  closeUniv 3 (integer_sum_scale _ _ _)
theorem integer_sum_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (addedSum (var 0) (var 1) (var 2)) (add (integerSum (var 0) (var 2)) (integerSum (var 1) (var 2)))) :=
  closeUniv 3 (integer_sum_add _ _ _)

theorem sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      ((fstT (run (var 0) (var 1) (var 2)) ≐ commonD (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ rationalSum (var 0)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ rationalSum (var 1)) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐
                integerSum (sourceNumerators (var 0) (var 1) (var 2)) (length (var 0))) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐
                integerSum (targetNumerators (var 0) (var 1) (var 2)) (length (var 1))))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_denominator _ _ _) (.andI (returned_source _ _ _)
    (.andI (returned_target _ _ _) (.andI (returned_source_integer _ _ _) (returned_target_integer _ _ _))))))

theorem returned_sums_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (represents (fstT (sndT (run (var 0) (var 1) (var 2))))
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) (fstT (run (var 0) (var 1) (var 2))) ⋏
      represents (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))))
        (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))))) (fstT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (returned_source_represents _ _ _) (returned_target_represents _ _ _))

end LeanProofs.IPRA.Analysis.GaussianHornerCommonDenominator
