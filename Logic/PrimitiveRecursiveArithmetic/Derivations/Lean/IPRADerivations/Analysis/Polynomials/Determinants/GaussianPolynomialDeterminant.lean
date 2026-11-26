import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantTerms

/-!
# A runtime polynomial determinant by actual numeric permutation words

The actual program folds the signed polynomial products of the stored
permutation scan. Its width is m*L+1. Coefficient and evaluator Leibniz
formulas follow from genuine QF inductions over the computed list; the
word codec proves coverage and uniqueness for every numerical tuple.
The orientation is M(digit_j,j), with positive even and negative odd sign.
Row multilinearity, alternation, determinant multiplication, Vandermonde,
norm nonvanishing and fiber/annihilator conclusions are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_lookup zeros_evaluation added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (evaluate_congr canonical_coefficients_congr zeros_congr zeros_canonical added_canonical)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms
  (tableShape signPoint scalarProduct term)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def wordCode (m t : PTm n) : PTm n := entry (Foundations.RuntimePermutationWords.words m) t
def summand (M m L t : PTm n) : PTm n := term M m L (wordCode m t)
def data (M m L : PTm n) : PTm n := pairT M (pairT m L)
def width (m L : PTm n) : PTm n := succ (m*L)
def initial : PTm 1 := zeros (width (fstT (sndT (var 0))) (sndT (sndT (var 0))))
def stepBody : PTm 3 := added (var 1)
  (summand (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0))
  (width (fstT (sndT (var 2))) (sndT (sndT (var 2))))
def prefixF : PR 2 := rec2 initial stepBody
def partialDeterminant (M m L t : PTm n) : PTm n := ap2 prefixF t (data M m L)
def determinant (M m L : PTm n) : PTm n := partialDeterminant M m L (Foundations.RuntimePermutationWords.count m)
def coefficientTerm (M m L t s : PTm n) : PTm n := qmul (signPoint m (wordCode m t))
  (entry (GaussianPolynomialDeterminantTerms.stage M m L (wordCode m t) m) s)
def valueTerm (M m L t z : PTm n) : PTm n := qmul (signPoint m (wordCode m t))
  (scalarProduct M m L (wordCode m t) z m)
def coefficientBody : PTm 2 := coefficientTerm (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (var 0) (sndT (sndT (sndT (var 1))))
def valueBody : PTm 2 := valueTerm (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (var 0) (sndT (sndT (sndT (var 1))))
def coefficientSum (M m L t s : PTm n) : PTm n := GaussianRationalFiniteSum.sum coefficientBody t
  (GaussianPolynomialDeterminantTerms.data M m L s)
def valueSum (M m L t z : PTm n) : PTm n := GaussianRationalFiniteSum.sum valueBody t
  (GaussianPolynomialDeterminantTerms.data M m L z)

ipra_subst wordCode
ipra_subst summand
ipra_subst data
ipra_subst width
ipra_subst partialDeterminant
ipra_subst determinant
ipra_subst coefficientTerm
ipra_subst valueTerm
ipra_subst coefficientSum
ipra_subst valueSum

theorem summand_congr {M M' m m' L L' t t' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hL : Γ ⊢[PRAAx] L ≐ L') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    summand M m L t ≐ summand M' m' L' t' := by
  ipra_congr (summand (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hM, hm, hL, ht]
theorem added_congr {P P' Q Q' b b' : PTm n}
    (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    added P Q b ≐ added P' Q' b' := by
  ipra_congr (added (var 0) (var 1) (var 2) : PTm 3) with [hP, hQ, hb]
theorem partial_congr {M M' m m' L L' t t' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hL : Γ ⊢[PRAAx] L ≐ L') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    partialDeterminant M m L t ≐ partialDeterminant M' m' L' t' := by
  ipra_congr (partialDeterminant (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hM, hm, hL, ht]
theorem prefix_zero (M m L : PTm n) : Γ ⊢[PRAAx] partialDeterminant M m L zero ≐ zeros (width m L) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data M m L)
  simp only [initial,GaussianRationalPolynomialBuffers.subst_zeros,subst_width,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero] at e
  have tail := snd_pair (Γ := Γ) M (pairT m L)
  exact e.eqTrans (zeros_congr (congrSucc (congrMul tail.fstE
    tail.sndE)))
theorem prefix_succ (M m L t : PTm n) : Γ ⊢[PRAAx] partialDeterminant M m L (succ t) ≐
    added (partialDeterminant M m L t) (summand M m L t) (width m L) := by
  have e := rec2_succ (Γ := Γ) initial stepBody t (data M m L)
  simp only [stepBody,GaussianRationalPolynomialBuffers.subst_added,subst_summand,subst_width,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at e
  have tail := snd_pair (Γ := Γ) M (pairT m L)
  exact e.eqTrans (added_congr (.eqRefl _) (summand_congr (fst_pair _ _)
    tail.fstE tail.sndE (.eqRefl _))
      (congrSucc (congrMul tail.fstE tail.sndE)))

theorem prefix_length (M m L t : PTm n) : Γ ⊢[PRAAx] length (partialDeterminant M m L t) ≐ width m L := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_zero _ _ _))).eqTrans (zeros_length _)
  · exact (congrFst ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_succ _ _ _ _))).eqTrans (added_length _ _ _)
theorem prefix_canonical (M m L t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (partialDeterminant M m L t) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact canonical_coefficients_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_zero _ _ _)) (zeros_canonical _)
  · exact canonical_coefficients_congr ((partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (prefix_succ _ _ _ _)) (added_canonical _ _ _)

theorem coefficient_body_at (M m L t s : PTm n) : Γ ⊢[PRAAx]
    inst2 coefficientBody t (GaussianPolynomialDeterminantTerms.data M m L s) ≐ coefficientTerm M m L t s := by
  simp only [coefficientBody,inst2,subst_coefficientTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) M (pairT m (pairT L s))
  have rest := (congrSnd tail).eqTrans (snd_pair m (pairT L s))
  simpa using Prf.eqCongr (Γ := Γ) (coefficientTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (GaussianPolynomialDeterminantTerms.data M m L s),fstT (sndT (GaussianPolynomialDeterminantTerms.data M m L s)),
      fstT (sndT (sndT (GaussianPolynomialDeterminantTerms.data M m L s))),t,sndT (sndT (sndT (GaussianPolynomialDeterminantTerms.data M m L s)))])
    (σ' := ![M,m,L,t,s]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact tail.fstE
      · exact rest.fstE
      · exact .eqRefl _
      · exact rest.sndE)
theorem value_body_at (M m L t z : PTm n) : Γ ⊢[PRAAx]
    inst2 valueBody t (GaussianPolynomialDeterminantTerms.data M m L z) ≐ valueTerm M m L t z := by
  simp only [valueBody,inst2,subst_valueTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) M (pairT m (pairT L z))
  have rest := (congrSnd tail).eqTrans (snd_pair m (pairT L z))
  simpa using Prf.eqCongr (Γ := Γ) (valueTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (GaussianPolynomialDeterminantTerms.data M m L z),fstT (sndT (GaussianPolynomialDeterminantTerms.data M m L z)),
      fstT (sndT (sndT (GaussianPolynomialDeterminantTerms.data M m L z))),t,sndT (sndT (sndT (GaussianPolynomialDeterminantTerms.data M m L z)))])
    (σ' := ![M,m,L,t,z]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact tail.fstE
      · exact rest.fstE
      · exact .eqRefl _
      · exact rest.sndE)

theorem coefficient_sum_zero (M m L s : PTm n) : Γ ⊢[PRAAx] coefficientSum M m L zero s ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _
theorem coefficient_sum_succ (M m L t s : PTm n) : Γ ⊢[PRAAx]
    coefficientSum M m L (succ t) s ≐ qadd (coefficientSum M m L t s) (coefficientTerm M m L t s) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (coefficient_body_at _ _ _ _ _))
theorem value_sum_zero (M m L z : PTm n) : Γ ⊢[PRAAx] valueSum M m L zero z ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _
theorem value_sum_succ (M m L t z : PTm n) : Γ ⊢[PRAAx]
    valueSum M m L (succ t) z ≐ qadd (valueSum M m L t z) (valueTerm M m L t z) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (value_body_at _ _ _ _ _))

theorem prefix_coefficient (M m L t s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (partialDeterminant M m L t) s ≐ coefficientSum M m L t s := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift m*Syn.shift L) := by
    simpa only [Fm.shift,subst_le,PTm.subst_mul,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (entry (partialDeterminant (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0)) (Syn.shift s) ≐
      coefficientSum (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s)) := by
    ipra_qfind [subst_entry, subst_partialDeterminant, subst_coefficientSum]
    · exact (entry_congr (prefix_zero _ _ _) (.eqRefl _)).eqTrans
        ((zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs)).eqTrans (coefficient_sum_zero _ _ _ _).eqSymm)
    · exact (entry_congr (prefix_succ _ _ _ _) (.eqRefl _)).eqTrans
        ((added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans ss.wk)).eqTrans
          ((qadd_congr Prf.hyp0 (GaussianPolynomialDeterminantTerms.term_coefficient _ _ _ _ _ ss.wk)).eqTrans
            (coefficient_sum_succ _ _ _ _ _).eqSymm))
  simpa only [Fm.subst_eq,subst_entry,subst_partialDeterminant,subst_coefficientSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem prefix_evaluation (M m L t z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (partialDeterminant M m L t) z ≐ valueSum M m L t z := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (evaluate (partialDeterminant (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0)) (Syn.shift z) ≐
      valueSum (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift z)) := by
    ipra_qfind [GaussianRationalHorner.subst_evaluate, subst_partialDeterminant, subst_valueSum]
    · exact (evaluate_congr (prefix_zero _ _ _) (.eqRefl _)).eqTrans
        ((zeros_evaluation _ _).eqTrans (value_sum_zero _ _ _ _).eqSymm)
    · exact (evaluate_congr (prefix_succ _ _ _ _) (.eqRefl _)).eqTrans
        ((added_evaluation _ _ _ _ (prefix_length _ _ _ _) (GaussianPolynomialDeterminantTerms.term_length _ _ _ _)).eqTrans
          ((qadd_congr Prf.hyp0 (GaussianPolynomialDeterminantTerms.term_evaluation _ _ _ _ _ hs.wk)).eqTrans
            (value_sum_succ _ _ _ _ _).eqSymm))
  simpa only [Fm.subst_eq,GaussianRationalHorner.subst_evaluate,subst_partialDeterminant,subst_valueSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem determinant_length (M m L : PTm n) : Γ ⊢[PRAAx] length (determinant M m L) ≐ succ (m*L) := prefix_length _ _ _ _
theorem determinant_canonical (M m L : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (determinant M m L) := prefix_canonical _ _ _ _
/-- The displayed sum uses actual retained word codes. Its coverage and
uniqueness below identify precisely all numeric permutation tuples. -/
theorem coefficient_leibniz (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (determinant M m L) s ≐ coefficientSum M m L (Foundations.RuntimePermutationWords.count m) s :=
  prefix_coefficient _ _ _ _ _ hs
theorem evaluation_leibniz (M m L z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (determinant M m L) z ≐ valueSum M m L (Foundations.RuntimePermutationWords.count m) z :=
  prefix_evaluation _ _ _ _ _ h


theorem prefix_one_evaluation (M m L z : PTm n) : Γ ⊢[PRAAx]
    evaluate (partialDeterminant M m L one) z ≐ evaluate (summand M m L zero) z :=
  (evaluate_congr (prefix_succ _ _ _ zero) (.eqRefl _)).eqTrans
    ((added_evaluation _ _ _ _ (prefix_length _ _ _ _) (GaussianPolynomialDeterminantTerms.term_length _ _ _ _)).eqTrans
      ((qadd_congr ((evaluate_congr (prefix_zero _ _ _) (.eqRefl _)).eqTrans (zeros_evaluation _ _)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.horner_canonical _ _ _))))
theorem empty_evaluation (M L z : PTm n) : Γ ⊢[PRAAx] evaluate (determinant M zero L) z ≐ qone :=
  (evaluate_congr (partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Foundations.RuntimePermutationWords.count_zero) (.eqRefl _)).eqTrans
    ((prefix_one_evaluation _ _ _ _).eqTrans (GaussianPolynomialDeterminantTerms.empty_term_evaluation _ _ _ _))
theorem singleton_evaluation (M L z : PTm n) (h : Γ ⊢[PRAAx] tableShape M one L) : Γ ⊢[PRAAx]
    evaluate (determinant M one L) z ≐ evaluate (GaussianPolynomialDeterminantTerms.cell M zero zero) z :=
  (evaluate_congr (partial_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Foundations.RuntimePermutationWords.count_one) (.eqRefl _)).eqTrans
    ((prefix_one_evaluation _ _ _ _).eqTrans (GaussianPolynomialDeterminantTerms.singleton_term_evaluation _ _ _ _ h))

theorem retained_word (m t : PTm n) (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m)) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.permutation m (wordCode m t) :=
  Foundations.RuntimePermutationWords.retained_valid _ _ ht
theorem tuple_coverage (P m : PTm n) (h : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.tuple P m) : Γ ⊢[PRAAx]
    lt (Foundations.RuntimePermutationWords.position P m) (Foundations.RuntimePermutationWords.count m) ⋏
      (wordCode m (Foundations.RuntimePermutationWords.position P m) ≐ Foundations.RuntimePermutationWords.encode P m) :=
  Foundations.RuntimePermutationWords.listed _ _ h

def certificate (M m L z : PTm n) : Fm PTm n := (length (determinant M m L) ≐ width m L) ⋏
  (canonicalCoefficients (determinant M m L) ⋏
    (evaluate (determinant M m L) z ≐ valueSum M m L (Foundations.RuntimePermutationWords.count m) z))
ipra_subst certificate
theorem determinant_correct (M m L z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx] certificate M m L z :=
  .andI (determinant_length _ _ _) (.andI (determinant_canonical _ _ _) (evaluation_leibniz _ _ _ _ h))

/-! Literal PR3 output returns the actual polynomial and actual word list,
not a supplied coefficient table or a scalar evaluation-only matrix. -/
def output (M m L : PTm n) : PTm n := pairT (determinant M m L)
  (pairT (Foundations.RuntimePermutationWords.words m) (Foundations.RuntimePermutationWords.count m))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (M m L : PTm n) : PTm n := ap3 outputF M m L
ipra_subst output
ipra_subst run
theorem program_at (M m L : PTm n) : Γ ⊢[PRAAx] run M m L ≐ output M m L := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![M,m,L]
theorem returned_polynomial (M m L : PTm n) : Γ ⊢[PRAAx] fstT (run M m L) ≐ determinant M m L :=
  (program_at _ _ _).fstE
theorem returned_words (M m L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run M m L)) ≐ Foundations.RuntimePermutationWords.words m :=
  (program_at _ _ _).sndE.fstE
theorem returned_count (M m L : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run M m L)) ≐ Foundations.RuntimePermutationWords.count m :=
  (program_at _ _ _).sndE.sndE
theorem returned_length (M m L : PTm n) : Γ ⊢[PRAAx] length (fstT (run M m L)) ≐ succ (m*L) :=
  (congrFst (returned_polynomial _ _ _)).eqTrans (determinant_length _ _ _)
theorem returned_canonical (M m L : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (fstT (run M m L)) :=
  canonical_coefficients_congr (returned_polynomial _ _ _) (determinant_canonical _ _ _)
theorem returned_coefficient (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (fstT (run M m L)) s ≐ coefficientSum M m L (Foundations.RuntimePermutationWords.count m) s :=
  (entry_congr (returned_polynomial _ _ _) (.eqRefl _)).eqTrans (coefficient_leibniz _ _ _ _ hs)
theorem returned_evaluation (M m L z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (fstT (run M m L)) z ≐ valueSum M m L (Foundations.RuntimePermutationWords.count m) z :=
  (evaluate_congr (returned_polynomial _ _ _) (.eqRefl _)).eqTrans (evaluation_leibniz _ _ _ _ h)

theorem runtime_polynomial_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (determinant_correct _ _ _ _ Prf.hyp0))
theorem runtime_polynomial_determinant_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (determinant (var 0) (var 1) (var 2)) ≐ succ (var 1*var 2)) ⋏
      canonicalCoefficients (determinant (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (determinant_length _ _ _) (determinant_canonical _ _ _))
theorem runtime_coefficient_leibniz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1*var 2) ⟶ entry (determinant (var 0) (var 1) (var 2)) (var 3) ≐
      coefficientSum (var 0) (var 1) (var 2) (Foundations.RuntimePermutationWords.count (var 1)) (var 3)) :=
  closeUniv 4 (.impI (coefficient_leibniz _ _ _ _ Prf.hyp0))
theorem runtime_evaluation_leibniz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ evaluate (determinant (var 0) (var 1) (var 2)) (var 3) ≐
      valueSum (var 0) (var 1) (var 2) (Foundations.RuntimePermutationWords.count (var 1)) (var 3)) :=
  closeUniv 4 (.impI (evaluation_leibniz _ _ _ _ Prf.hyp0))
theorem runtime_permutation_coverage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Foundations.RuntimePermutationWords.tuple (var 0) (var 1) ⟶
      (lt (Foundations.RuntimePermutationWords.position (var 0) (var 1)) (Foundations.RuntimePermutationWords.count (var 1)) ⋏
        (wordCode (var 1) (Foundations.RuntimePermutationWords.position (var 0) (var 1)) ≐
          Foundations.RuntimePermutationWords.encode (var 0) (var 1)))) :=
  closeUniv 2 (.impI (tuple_coverage _ _ Prf.hyp0))
theorem empty_polynomial_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (determinant (var 0) zero (var 1)) (var 2) ≐ qone) := closeUniv 3 (empty_evaluation _ _ _)
theorem singleton_polynomial_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tableShape (var 0) one (var 1) ⟶ evaluate (determinant (var 0) one (var 1)) (var 2) ≐
      evaluate (GaussianPolynomialDeterminantTerms.cell (var 0) zero zero) (var 2)) :=
  closeUniv 3 (.impI (singleton_evaluation _ _ _ Prf.hyp0))
theorem runtime_determinant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem returned_determinant_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1*var 2) ⟶ entry (fstT (run (var 0) (var 1) (var 2))) (var 3) ≐
      coefficientSum (var 0) (var 1) (var 2) (Foundations.RuntimePermutationWords.count (var 1)) (var 3)) :=
  closeUniv 4 (.impI (returned_coefficient _ _ _ _ Prf.hyp0))
theorem returned_determinant_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ evaluate (fstT (run (var 0) (var 1) (var 2))) (var 3) ≐
      valueSum (var 0) (var 1) (var 2) (Foundations.RuntimePermutationWords.count (var 1)) (var 3)) :=
  closeUniv 4 (.impI (returned_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant
