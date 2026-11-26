import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalPermutationSum
import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialProductDegree

/-!
# Selecting the leading coefficient in the actual determinant sum

A bounded support condition on the retained terms gives a single stored
coefficient of the existing determinant. The degree proof uses the actual
least nonzero scan after checking all preceding coefficient slots.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantLeadingSelection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant
  (determinant coefficientTerm coefficientBody coefficient_body_at coefficient_leibniz)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction (spike_miss spike_hit spike_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPermutationSum (deltaSum delta_body_at delta_selected delta_outside)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (first degree)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree (first_exact leading)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_eq recode_congr zeroPrefix)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def supportedAt (M m L s r : PTm n) : Fm PTm n := .all
  (lt (var 0) (count (Syn.shift m)) ⟶ neg (var 0 ≐ Syn.shift r) ⟶
    coefficientTerm (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s) ≐ qzero)

@[simp] theorem subst_supportedAt {l : ℕ} (σ : Fin n → PTm l) (M m L s r : PTm n) :
    (supportedAt M m L s r).subst σ = supportedAt (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ s) (Syn.subst σ r) := by simp [supportedAt,Syn.subst_shift,Syn.shift_subst]

theorem supported_at (M m L s r t : PTm n) (h : Γ ⊢[PRAAx] supportedAt M m L s r)
    (ht : Γ ⊢[PRAAx] lt t (count m)) (hne : Γ ⊢[PRAAx] neg (t ≐ r)) :
    Γ ⊢[PRAAx] coefficientTerm M m L t s ≐ qzero := by
  have miss : Γ ⊢[PRAAx] lt t (count m) ⟶ neg (t ≐ r) ⟶ coefficientTerm M m L t s ≐ qzero := by
    simpa [supportedAt] using h.allE t
  exact .impE (.impE miss ht) hne

private theorem coefficient_spike (M m L s r t : PTm n)
    (h : Γ ⊢[PRAAx] supportedAt M m L s r) (ht : Γ ⊢[PRAAx] lt t (count m)) :
    Γ ⊢[PRAAx] inst2 coefficientBody t (GaussianPolynomialDeterminantTerms.data M m L s) ≐
      inst2 (GaussianRationalPermutationSum.deltaBody coefficientBody) t
        (pairT r (GaussianPolynomialDeterminantTerms.data M m L s)) := by
  have canonicalTerm := (recode_congr (coefficient_body_at (Γ := Γ) M m L t s)).eqTrans
    (recode_eq _ (qmul_canonical _ _))
  have delta := (delta_body_at coefficientBody r t (GaussianPolynomialDeterminantTerms.data M m L s)).eqTrans
    (spike_congr (.eqRefl _) canonicalTerm (.eqRefl _))
  refine (coefficient_body_at _ _ _ _ _).eqTrans (?_ : Γ ⊢[PRAAx] _ ≐ _)
  refine .orE (eq_or_ne t r) ?_ ?_
  · exact (delta.wk.eqTrans (spike_hit _ _ _ Prf.hyp0)).eqSymm
  · exact (supported_at M m L s r t h.wk ht.wk Prf.hyp0).eqTrans
      ((spike_miss _ _ _ Prf.hyp0).eqSymm.eqTrans delta.wk.eqSymm)

theorem coefficient_as_delta (M m L s r : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L))
    (h : Γ ⊢[PRAAx] supportedAt M m L s r) : Γ ⊢[PRAAx]
    entry (determinant M m L) s ≐ deltaSum coefficientBody (count m) r (GaussianPolynomialDeterminantTerms.data M m L s) := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] supportedAt (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift s) (Syn.shift r) := by
    simpa only [Fm.shift,subst_supportedAt,Syn.shift] using h.shift
  refine (coefficient_leibniz M m L s hs).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded coefficientBody (GaussianRationalPermutationSum.deltaBody coefficientBody)
      (count m) (GaussianPolynomialDeterminantTerms.data M m L s) (pairT r (GaussianPolynomialDeterminantTerms.data M m L s)) ?_)
  refine .allI (.impI ?_)
  simpa [Syn.shift] using coefficient_spike (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift s)
    (Syn.shift r) (var 0) shifted.wk Prf.hyp0

theorem selected_coefficient (M m L s r : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L))
    (hr : Γ ⊢[PRAAx] lt r (count m)) (h : Γ ⊢[PRAAx] supportedAt M m L s r) :
    Γ ⊢[PRAAx] entry (determinant M m L) s ≐ coefficientTerm M m L r s :=
  (coefficient_as_delta M m L s r hs h).eqTrans
    ((delta_selected _ _ _ _ hr).eqTrans
      ((recode_congr (coefficient_body_at _ _ _ _ _)).eqTrans (recode_eq _ (qmul_canonical _ _))))

theorem zero_coefficient (M m L s r : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L))
    (hr : Γ ⊢[PRAAx] le (count m) r) (h : Γ ⊢[PRAAx] supportedAt M m L s r) :
    Γ ⊢[PRAAx] entry (determinant M m L) s ≐ qzero :=
  (coefficient_as_delta M m L s r hs h).eqTrans (delta_outside _ _ _ _ hr)

def earlierTermsZero (M m L s : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift s) ⟶ supportedAt (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (count (Syn.shift m)))

theorem zero_prefix (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L))
    (h : Γ ⊢[PRAAx] earlierTermsZero M m L s) : Γ ⊢[PRAAx] zeroPrefix (determinant M m L) s := by
  have shiftedBound : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift m*Syn.shift L) := by
    simpa only [Fm.shift,subst_le,PTm.subst_mul,Syn.shift] using hs.shift
  refine .allI (.impI ?_)
  have localPrefix := h.allOpen
  have support := Prf.impE localPrefix.wk Prf.hyp0
  have zero := zero_coefficient (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (count (Syn.shift m))
    (le_trans (le_of_lt Prf.hyp0) shiftedBound.wk) (le_refl _) support
  simpa [Syn.shift] using (recode_congr zero).eqTrans (recode_eq _ GaussianRationalSyntheticDivision.qzero_canonical)

def input (M m L s r : PTm n) : Fm PTm n := (le s (m*L)) ⋏
  (lt r (count m) ⋏ (earlierTermsZero M m L s ⋏
    (supportedAt M m L s r ⋏ neg (coefficientTerm M m L r s ≐ qzero))))

def certificate (M m L s r : PTm n) : Fm PTm n := (first (determinant M m L) (m*L) ≐ s) ⋏
  (degree (determinant M m L) (m*L) ≐ monus (m*L) s) ⋏
    (leading (determinant M m L) (m*L) ≐ coefficientTerm M m L r s)

theorem selected_leading (M m L s r : PTm n) (h : Γ ⊢[PRAAx] input M m L s r) :
    Γ ⊢[PRAAx] certificate M m L s r := by
  have sBound := Prf.andE₁ h
  have conditions := Prf.andE₂ h
  have rBound := Prf.andE₁ conditions
  have early := Prf.andE₁ (Prf.andE₂ conditions)
  have selected := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ conditions))
  have nonzero := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ conditions))
  have atSlot := (recode_congr (selected_coefficient M m L s r sBound rBound selected)).eqTrans
    (recode_eq _ (qmul_canonical _ _))
  have firstSlot := first_exact _ _ _ sBound (zero_prefix M m L s sBound early)
    (.impI (.impE nonzero.wk (atSlot.wk.eqSymm.eqTrans Prf.hyp0)))
  exact .andI firstSlot (.andI (congrMonus (.eqRefl _) firstSlot)
    ((recode_congr (entry_congr (.eqRefl _) firstSlot)).eqTrans atSlot))

theorem actual_selected_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (selected_leading _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantLeadingSelection
