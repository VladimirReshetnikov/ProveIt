import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantLeadingSelection
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantTermDegree

/-!
# A unique maximal computed degree in the retained determinant terms

Each retained term is the original unsigned stage with its original sign.
Strict degree dominance over the other successful stages gives the actual
leading-slot support, with zero coefficients supplied by the failed stages.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantDegreeDominance

open_ipra
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant (determinant wordCode coefficientTerm)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (stage stage_congr signPoint sign_canonical)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTermDegree (first_congr sign_nonzero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantLeadingSelection (supportedAt earlierTermsZero)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (first flag degree all_zero_of_flag_zero flag_cases success_index first_zero_prefix
    flag_one_of_found found_of_flag_one nonzero_of_flag_one)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree
  (leading leading_canonical leading_nonzero raw_zero_right multiply_nonzero)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (zero_prefix_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr add_lt_left)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def retainedStage (M m B r : PTm n) : PTm n := stage M m B (wordCode m r) m

ipra_subst retainedStage

theorem retained_stage_congr (M m B : PTm n) {r s : PTm n} (h : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] retainedStage M m B r ≐ retainedStage M m B s :=
  stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (entry_congr (.eqRefl _) h) (.eqRefl _)

def strictDominance (M m B r : PTm n) : Fm PTm n := .all
  (lt (var 0) (count (Syn.shift m)) ⟶ neg (var 0 ≐ Syn.shift r) ⟶
    flag (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (var 0)) (Syn.shift m*Syn.shift B) ≐ one ⟶
    lt (degree (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (var 0)) (Syn.shift m*Syn.shift B))
      (degree (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r)) (Syn.shift m*Syn.shift B)))

ipra_subst strictDominance [Syn.subst_shift, Syn.shift_subst]

theorem strict_at (M m B r s : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hs : Γ ⊢[PRAAx] lt s (count m)) (hne : Γ ⊢[PRAAx] neg (s ≐ r))
    (hf : Γ ⊢[PRAAx] flag (retainedStage M m B s) (m*B) ≐ one) : Γ ⊢[PRAAx]
    lt (degree (retainedStage M m B s) (m*B)) (degree (retainedStage M m B r) (m*B)) := by
  have above : Γ ⊢[PRAAx] lt s (count m) ⟶ neg (s ≐ r) ⟶ flag (retainedStage M m B s) (m*B) ≐ one ⟶
      lt (degree (retainedStage M m B s) (m*B)) (degree (retainedStage M m B r) (m*B)) := by
    simpa [strictDominance] using h.allE s
  exact .impE (.impE (.impE above hs) hne) hf

private theorem first_degree_total (P N : PTm n) (h : Γ ⊢[PRAAx] flag P N ≐ one) :
    Γ ⊢[PRAAx] first P N+degree P N ≐ N := (eq_add_of_le (success_index P N h)).eqSymm

theorem degree_lt_first_gt (P Q N : PTm n) (hp : Γ ⊢[PRAAx] flag P N ≐ one) (hq : Γ ⊢[PRAAx] flag Q N ≐ one)
    (hd : Γ ⊢[PRAAx] lt (degree Q N) (degree P N)) : Γ ⊢[PRAAx] lt (first P N) (first Q N) := by
  have right := (first_degree_total P N hp).eqTrans (first_degree_total Q N hq).eqSymm
  have strict := add_lt_left (first P N) hd
  exact le_of_add_le_add_right (le_congr (by ipra_ring) right strict)

theorem earlier_coefficient_zero (M m B s i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (first (retainedStage M m B s) (m*B))) :
    Γ ⊢[PRAAx] coefficientTerm M m B s i ≐ qzero :=
  raw_zero_right _ _ (zero_prefix_at _ _ _ (first_zero_prefix _ _) hi)

theorem failed_coefficient_zero (M m B s i : PTm n)
    (hf : Γ ⊢[PRAAx] flag (retainedStage M m B s) (m*B) ≐ zero) (hi : Γ ⊢[PRAAx] le i (m*B)) :
    Γ ⊢[PRAAx] coefficientTerm M m B s i ≐ qzero :=
  raw_zero_right _ _ (zero_prefix_at _ _ _ (all_zero_of_flag_zero _ _ hf) ((succ_monus_succ _ _).eqTrans hi))

theorem coefficient_before_selected (M m B r s i : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hrf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one) (hs : Γ ⊢[PRAAx] lt s (count m))
    (hi : Γ ⊢[PRAAx] lt i (first (retainedStage M m B r) (m*B))) : Γ ⊢[PRAAx] coefficientTerm M m B s i ≐ qzero := by
  refine .orE (flag_cases (retainedStage M m B s) (m*B)) ?_ ?_
  · exact failed_coefficient_zero _ _ _ _ _ Prf.hyp0
      (le_trans (le_of_lt hi.wk) (success_index _ _ hrf.wk))
  · refine .orE (eq_or_ne s r) ?_ ?_
    · have he : (s ≐ r) :: (flag (retainedStage M m B s) (m*B) ≐ one) :: Γ ⊢[PRAAx]
          first (retainedStage M m B s) (m*B) ≐ first (retainedStage M m B r) (m*B) :=
        first_congr (retained_stage_congr M m B Prf.hyp0) (.eqRefl _)
      exact earlier_coefficient_zero _ _ _ _ _ (lt_congr (.eqRefl _) he.eqSymm hi.wk.wk)
    · have hd := strict_at M m B r s h.wk.wk hs.wk.wk Prf.hyp0 Prf.hyp1
      exact earlier_coefficient_zero _ _ _ _ _
        (lt_of_le_of_lt (le_of_lt hi.wk.wk) (degree_lt_first_gt _ _ _ hrf.wk.wk Prf.hyp1 hd))

theorem off_rank_coefficient_zero (M m B r s : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hrf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one)
    (hs : Γ ⊢[PRAAx] lt s (count m)) (hne : Γ ⊢[PRAAx] neg (s ≐ r)) : Γ ⊢[PRAAx]
    coefficientTerm M m B s (first (retainedStage M m B r) (m*B)) ≐ qzero := by
  refine .orE (flag_cases (retainedStage M m B s) (m*B)) ?_ ?_
  · exact failed_coefficient_zero _ _ _ _ _ Prf.hyp0 (success_index _ _ hrf.wk)
  · exact earlier_coefficient_zero _ _ _ _ _ (degree_lt_first_gt _ _ _ hrf.wk Prf.hyp0
      (strict_at M m B r s h.wk hs.wk hne.wk Prf.hyp0))

theorem off_rank_support (M m B r : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one) : Γ ⊢[PRAAx]
    supportedAt M m B (first (retainedStage M m B r) (m*B)) r := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] strictDominance (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have flagShift : Γ.map Fm.shift ⊢[PRAAx] flag (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r))
      (Syn.shift m*Syn.shift B) ≐ one := by simpa [Fm.shift,Syn.shift] using hf.shift
  refine .allI (.impI (.impI ?_))
  simpa [Syn.shift] using off_rank_coefficient_zero (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) (var 0)
    shifted.wk.wk flagShift.wk.wk Prf.hyp1 Prf.hyp0

private theorem earlier_slot_support (M m B r i : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one)
    (hi : Γ ⊢[PRAAx] lt i (first (retainedStage M m B r) (m*B))) : Γ ⊢[PRAAx] supportedAt M m B i (count m) := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] strictDominance (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have flagShift : Γ.map Fm.shift ⊢[PRAAx] flag (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r))
      (Syn.shift m*Syn.shift B) ≐ one := by simpa [Fm.shift,Syn.shift] using hf.shift
  have indexShift : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i)
      (first (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r)) (Syn.shift m*Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using hi.shift
  refine .allI (.impI (.impI ?_))
  simpa [Syn.shift] using coefficient_before_selected
    (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) (var 0) (Syn.shift i)
    shifted.wk.wk flagShift.wk.wk Prf.hyp1 indexShift.wk.wk

theorem earlier_support (M m B r : PTm n) (h : Γ ⊢[PRAAx] strictDominance M m B r)
    (hf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one) : Γ ⊢[PRAAx]
    earlierTermsZero M m B (first (retainedStage M m B r) (m*B)) := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] strictDominance (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have flagShift : Γ.map Fm.shift ⊢[PRAAx] flag (retainedStage (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r))
      (Syn.shift m*Syn.shift B) ≐ one := by simpa [Fm.shift,Syn.shift] using hf.shift
  refine .allI (.impI ?_)
  simpa [Syn.shift] using earlier_slot_support (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift r) (var 0)
    shifted.wk flagShift.wk Prf.hyp0

def signedLeading (M m B r : PTm n) : PTm n :=
  qmul (signPoint m (wordCode m r)) (leading (retainedStage M m B r) (m*B))

theorem coefficient_at_selected_first (M m B r : PTm n) : Γ ⊢[PRAAx]
    coefficientTerm M m B r (first (retainedStage M m B r) (m*B)) ≐ signedLeading M m B r :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm

theorem signed_leading_nonzero (M m B r : PTm n) (hf : Γ ⊢[PRAAx] flag (retainedStage M m B r) (m*B) ≐ one) :
    Γ ⊢[PRAAx] neg (signedLeading M m B r ≐ qzero) :=
  multiply_nonzero _ _ (sign_canonical _ _) (leading_canonical _ _)
    (sign_nonzero _ _) (leading_nonzero _ _ (nonzero_of_flag_one _ _ hf))

def input (M m B r : PTm n) : Fm PTm n := lt r (count m) ⋏
  (flag (retainedStage M m B r) (m*B) ≐ one ⋏ strictDominance M m B r)

def certificate (M m B r : PTm n) : Fm PTm n := flag (determinant M m B) (m*B) ≐ one ⋏
  (degree (determinant M m B) (m*B) ≐ degree (retainedStage M m B r) (m*B) ⋏
    leading (determinant M m B) (m*B) ≐ signedLeading M m B r)

theorem determinant_dominance (M m B r : PTm n) (h : Γ ⊢[PRAAx] input M m B r) :
    Γ ⊢[PRAAx] certificate M m B r := by
  have hr := Prf.andE₁ h
  have hf := Prf.andE₁ (Prf.andE₂ h)
  have dom := Prf.andE₂ (Prf.andE₂ h)
  have bound := success_index _ _ hf
  have nz := signed_leading_nonzero M m B r hf
  have term := coefficient_at_selected_first (Γ := Γ) M m B r
  have termNZ := Prf.impI (Prf.impE nz.wk (term.wk.eqSymm.eqTrans Prf.hyp0))
  have result := GaussianPolynomialDeterminantLeadingSelection.selected_leading M m B _ r
    (.andI bound (.andI hr (.andI (earlier_support M m B r dom hf) (.andI (off_rank_support M m B r dom hf) termNZ))))
  have actualFound := lt_congr (Prf.andE₁ result).eqSymm (.eqRefl _) (found_of_flag_one _ _ hf)
  exact .andI (flag_one_of_found _ _ actualFound)
    (.andI (Prf.andE₁ (Prf.andE₂ result)) ((Prf.andE₂ (Prf.andE₂ result)).eqTrans term))

theorem actual_determinant_dominance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (determinant_dominance _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantDegreeDominance
