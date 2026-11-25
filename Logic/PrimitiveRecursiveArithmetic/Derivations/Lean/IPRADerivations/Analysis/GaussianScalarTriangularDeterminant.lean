import IPRADerivations.Analysis.GaussianScalarIdentityDeterminant
import IPRADerivations.Foundations.RuntimePermutationDigitSum
import IPRADerivations.Core.LinearCombination

/-!
# The actual numerical triangular determinant

The existing determinant and its retained permutation scan are used
unchanged. A genuine natural sum reflection shows that a nonidentity
permutation has both an excessive and a deficient digit. Thus either
orientation of field-zero triangular cells kills every nonidentity term.
The actual identity term is the existing Gaussian diagonal product.

This is a concrete kernel for the Newton change-of-basis route to the
Vandermonde product; no Vandermonde or block determinant law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarTriangularDeterminant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit digitBody data horizon permutationBit count retained_bound retained_valid)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB)
open LeanProofs.IPRA.Analysis.GaussianScalarIdentityDeterminant
  (identityWord identityRank identity_digit identity_sign identity_word_bound identity_rank_bound identity_rank_word)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (scalarDet rawProduct factorBody factorData signedTerm signedBody)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! A natural sum-order reflection, with only the two body schemas fixed. -/
def gapBody (f g : PTm 2) : PTm 2 := monus g f
@[simp] theorem gap_body_at (f g : PTm 2) (i x : PTm n) :
    inst2 (gapBody f g) i x = monus (inst2 g i x) (inst2 f i x) := by simp [gapBody,inst2]

theorem sum_gap_balance (f g : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x)))) : Γ ⊢[PRAAx]
    ap2 (sumF f) N x + ap2 (sumF (gapBody f g)) N x ≐ ap2 (sumF g) N x := by
  refine (LeanProofs.IPRA.sum_add f (gapBody f g) N x).eqSymm.eqTrans ?_
  refine LeanProofs.IPRA.sum_congr_bounded (LeanProofs.IPRA.addBody f (gapBody f g)) g x x N (.allI (.impI ?_))
  simpa only [LeanProofs.IPRA.inst2_addBody,gap_body_at] using (eq_add_of_le (.impE h.allOpen.wk Prf.hyp0)).eqSymm

theorem sum_gap_zero (f g : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x))))
    (hSum : Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF g) N x) : Γ ⊢[PRAAx]
    ap2 (sumF (gapBody f g)) N x ≐ zero := by
  ipra_lc natEq (sum_gap_balance f g N x h) - natEq hSum

theorem equal_term_of_order_and_sum (f g : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x))))
    (hSum : Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF g) N x) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 f i x ≐ inst2 g i x := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ le (inst2 f i x) (inst2 g i x) := by simpa using h.allE i
  have reverse : Γ ⊢[PRAAx] le (inst2 g i x) (inst2 f i x) := by
    simpa only [le,gap_body_at] using sum_zero_elim (gapBody f g) (sum_gap_zero f g N x h hSum) hi
  exact le_antisymm (.impE rule hi) reverse

def comparisonBody (f g : PTm 2) : PTm 2 := eqb (monus f g) zero
def comparison (f g : PTm 2) (N x : PTm n) : PTm n := allB (comparisonBody f g) N x
def firstBad (f g : PTm 2) (N x : PTm n) : PTm n := Search.mu (comparisonBody f g) N x
@[simp] theorem subst_comparison {k : ℕ} (σ : Fin n → PTm k) (f g : PTm 2) (N x : PTm n) :
    Syn.subst σ (comparison f g N x) = comparison f g (Syn.subst σ N) (Syn.subst σ x) := by simp [comparison,allB]
@[simp] theorem subst_firstBad {k : ℕ} (σ : Fin n → PTm k) (f g : PTm 2) (N x : PTm n) :
    Syn.subst σ (firstBad f g N x) = firstBad f g (Syn.subst σ N) (Syn.subst σ x) := by simp [firstBad,Search.mu]
@[simp] theorem comparison_body_at (f g : PTm 2) (i x : PTm n) :
    inst2 (comparisonBody f g) i x = eqb (monus (inst2 f i x) (inst2 g i x)) zero := by simp [comparisonBody,inst2]
theorem comparison_at (f g : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] comparison f g N x ≐ one)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] le (inst2 f i x) (inst2 g i x) := by
  have nonzero := Foundations.BoundedReflection.all_elim (f := comparisonBody f g) h hi
  exact AnalyticNumberTheory.Valuation.eq_of_eqb_ne (by simpa only [comparison_body_at] using nonzero)
theorem comparison_all (f g : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] comparison f g N x ≐ one) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] comparison f g (Syn.shift N) (Syn.shift x) ≐ one := by
    simpa [Fm.shift,Syn.shift] using h.shift
  exact .allI (.impI (comparison_at f g (Syn.shift N) (Syn.shift x) (var 0) hs.wk Prf.hyp0))
theorem comparison_failure (f g : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] comparison f g N x ≐ zero) : Γ ⊢[PRAAx]
    lt (firstBad f g N x) N ⋏ lt (inst2 g (firstBad f g N x) x) (inst2 f (firstBad f g N x) x) := by
  have failed := Foundations.BoundedReflection.all_fail (f := comparisonBody f g) h
  have different : Γ ⊢[PRAAx] neg (monus (inst2 f (firstBad f g N x) x) (inst2 g (firstBad f g N x) x) ≐ zero) :=
    AnalyticNumberTheory.Valuation.ne_of_eqb_zero (by simpa only [comparison_body_at,firstBad] using Prf.andE₂ failed)
  refine .andI (.andE₁ failed) (.orE (lt_or_le (inst2 g (firstBad f g N x) x) (inst2 f (firstBad f g N x) x)) Prf.hyp0 ?_)
  exact .botE _ (.impE different.wk Prf.hyp0)

theorem permutation_sum (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) : Γ ⊢[PRAAx]
    ap2 (sumF digitBody) m (data m w) ≐ ap2 (sumF (var 0 : PTm 2)) m (data m w) := by
  refine (Foundations.RuntimePermutationDigitSum.permutation_total m w hw hp).eqTrans ?_
  refine LeanProofs.IPRA.sum_congr_bounded (var 0 : PTm 2) (var 0 : PTm 2) zero (data m w) m (.allI (.impI ?_))
  exact .eqRefl _

theorem word_of_digits (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶ digit (Syn.shift m) (Syn.shift w) (var 0) ≐ var 0)) :
    Γ ⊢[PRAAx] w ≐ identityWord m := by
  refine Foundations.RuntimePermutationWords.word_unique _ _ _ hw (identity_word_bound m) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have digitEq : Δ ⊢[PRAAx] digit (Syn.shift m) (Syn.shift w) (var 0) ≐ var 0 := .impE h.allOpen.wk Prf.hyp0
  have identityEq : Δ ⊢[PRAAx] digit (Syn.shift m) (identityWord (Syn.shift m)) (var 0) ≐ var 0 := identity_digit _ _ Prf.hyp0
  have actual := (Foundations.RuntimePermutationWords.word_lookup (Γ := Δ) (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0).eqTrans
    (digitEq.eqTrans (identityEq.eqSymm.eqTrans
      (Foundations.RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm))
  simpa only [Δ,Syn.shift,Foundations.RuntimePermutationWords.subst_word,GaussianScalarIdentityDeterminant.subst_identityWord] using actual

theorem below_word (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (h : Γ ⊢[PRAAx] comparison digitBody (var 0 : PTm 2) m (data m w) ≐ one) : Γ ⊢[PRAAx] w ≐ identityWord m := by
  have totals := permutation_sum m w hw hp
  refine word_of_digits m w hw (.allI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] comparison digitBody (var 0 : PTm 2) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) ≐ one := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have os := comparison_all digitBody (var 0 : PTm 2) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) hs
  have ts : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF digitBody) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) ≐
      ap2 (sumF (var 0 : PTm 2)) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) := by
    simpa [Fm.shift,Syn.shift] using totals.shift
  have e := equal_term_of_order_and_sum digitBody (var 0 : PTm 2) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) (var 0) os.wk ts.wk Prf.hyp0
  exact (Foundations.RuntimePermutationWords.digit_body_at _ _ _).eqSymm.eqTrans (by simpa [inst2] using e)

theorem above_word (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (h : Γ ⊢[PRAAx] comparison (var 0 : PTm 2) digitBody m (data m w) ≐ one) : Γ ⊢[PRAAx] w ≐ identityWord m := by
  have totals := (permutation_sum m w hw hp).eqSymm
  refine word_of_digits m w hw (.allI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] comparison (var 0 : PTm 2) digitBody (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) ≐ one := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have os := comparison_all (var 0 : PTm 2) digitBody (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) hs
  have ts : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (var 0 : PTm 2)) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) ≐
      ap2 (sumF digitBody) (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) := by
    simpa [Fm.shift,Syn.shift] using totals.shift
  have e := equal_term_of_order_and_sum (var 0 : PTm 2) digitBody (Syn.shift m) (data (Syn.shift m) (Syn.shift w)) (var 0) os.wk ts.wk Prf.hyp0
  exact (Foundations.RuntimePermutationWords.digit_body_at _ _ _).eqSymm.eqTrans (by simpa [inst2] using e.eqSymm)

def excessIndex (m w : PTm n) : PTm n := firstBad digitBody (var 0 : PTm 2) m (data m w)
def deficitIndex (m w : PTm n) : PTm n := firstBad (var 0 : PTm 2) digitBody m (data m w)
@[simp] theorem position_body_at (i x : PTm n) : inst2 (var 0 : PTm 2) i x = i := by simp [inst2]
@[simp] theorem subst_excessIndex {k : ℕ} (σ : Fin n → PTm k) (m w : PTm n) :
    Syn.subst σ (excessIndex m w) = excessIndex (Syn.subst σ m) (Syn.subst σ w) := by simp [excessIndex]
@[simp] theorem subst_deficitIndex {k : ℕ} (σ : Fin n → PTm k) (m w : PTm n) :
    Syn.subst σ (deficitIndex m w) = deficitIndex (Syn.subst σ m) (Syn.subst σ w) := by simp [deficitIndex]

theorem excess_found (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) (hne : Γ ⊢[PRAAx] neg (w ≐ identityWord m)) : Γ ⊢[PRAAx]
    lt (excessIndex m w) m ⋏ lt (excessIndex m w) (digit m w (excessIndex m w)) := by
  have failed : Γ ⊢[PRAAx] comparison digitBody (var 0 : PTm 2) m (data m w) ≐ zero := by
    refine .orE (Foundations.BoundedReflection.all_cases (comparisonBody digitBody (var 0 : PTm 2)) m (data m w)) Prf.hyp0 ?_
    exact .botE _ (.impE hne.wk (below_word m w hw.wk hp.wk Prf.hyp0))
  have found := comparison_failure digitBody (var 0 : PTm 2) m (data m w) failed
  have order : Γ ⊢[PRAAx] lt (excessIndex m w) (inst2 digitBody (excessIndex m w) (data m w)) := by
    simpa only [position_body_at,excessIndex] using Prf.andE₂ found
  exact .andI (.andE₁ found) (lt_congr (.eqRefl _) (Foundations.RuntimePermutationWords.digit_body_at _ _ _) order)

theorem deficit_found (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) (hne : Γ ⊢[PRAAx] neg (w ≐ identityWord m)) : Γ ⊢[PRAAx]
    lt (deficitIndex m w) m ⋏ lt (digit m w (deficitIndex m w)) (deficitIndex m w) := by
  have failed : Γ ⊢[PRAAx] comparison (var 0 : PTm 2) digitBody m (data m w) ≐ zero := by
    refine .orE (Foundations.BoundedReflection.all_cases (comparisonBody (var 0 : PTm 2) digitBody) m (data m w)) Prf.hyp0 ?_
    exact .botE _ (.impE hne.wk (above_word m w hw.wk hp.wk Prf.hyp0))
  have found := comparison_failure (var 0 : PTm 2) digitBody m (data m w) failed
  have order : Γ ⊢[PRAAx] lt (inst2 digitBody (deficitIndex m w) (data m w)) (deficitIndex m w) := by
    simpa only [position_body_at,deficitIndex] using Prf.andE₂ found
  exact .andI (.andE₁ found) (lt_congr (Foundations.RuntimePermutationWords.digit_body_at _ _ _) (.eqRefl _) order)

def belowRow (A m r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶ lt (var 0) (Syn.shift r) ⟶
  recode (cell (Syn.shift A) (Syn.shift r) (var 0)) ≐ qzero)
def aboveRow (A m r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶ lt (Syn.shift r) (var 0) ⟶
  recode (cell (Syn.shift A) (Syn.shift r) (var 0)) ≐ qzero)
def belowZeros (A m : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶ belowRow (Syn.shift A) (Syn.shift m) (var 0))
def aboveZeros (A m : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶ aboveRow (Syn.shift A) (Syn.shift m) (var 0))
def triangular (A m : PTm n) : Fm PTm n := belowZeros A m ⋎ aboveZeros A m
def diagonalBody : PTm 2 := cell (var 1) (var 0) (var 0)
def diagonalProduct (A m : PTm n) : PTm n := GaussianRationalFiniteProduct.qprod diagonalBody m A
@[simp] theorem subst_belowRow {k : ℕ} (σ : Fin n → PTm k) (A m r : PTm n) :
    (belowRow A m r).subst σ = belowRow (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ r) := by simp [belowRow,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_aboveRow {k : ℕ} (σ : Fin n → PTm k) (A m r : PTm n) :
    (aboveRow A m r).subst σ = aboveRow (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ r) := by simp [aboveRow,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_belowZeros {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    (belowZeros A m).subst σ = belowZeros (Syn.subst σ A) (Syn.subst σ m) := by simp [belowZeros,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_aboveZeros {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    (aboveZeros A m).subst σ = aboveZeros (Syn.subst σ A) (Syn.subst σ m) := by simp [aboveZeros,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_triangular {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    (triangular A m).subst σ = triangular (Syn.subst σ A) (Syn.subst σ m) := by simp [triangular]
@[simp] theorem subst_diagonalProduct {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    Syn.subst σ (diagonalProduct A m) = diagonalProduct (Syn.subst σ A) (Syn.subst σ m) := by simp [diagonalProduct]
@[simp] theorem diagonal_body_at (A j : PTm n) : inst2 diagonalBody j A = cell A j j := by simp [diagonalBody,inst2]

theorem below_at (A m r j : PTm n) (h : Γ ⊢[PRAAx] belowZeros A m)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hjr : Γ ⊢[PRAAx] lt j r) :
    Γ ⊢[PRAAx] recode (cell A r j) ≐ qzero := by
  have row : Γ ⊢[PRAAx] lt r m ⟶ belowRow A m r := by simpa [belowZeros] using h.allE r
  have entry : Γ ⊢[PRAAx] lt j m ⟶ lt j r ⟶ recode (cell A r j) ≐ qzero := by
    simpa [belowRow] using (Prf.impE row hr).allE j
  exact .impE (.impE entry hj) hjr
theorem above_at (A m r j : PTm n) (h : Γ ⊢[PRAAx] aboveZeros A m)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) (hrj : Γ ⊢[PRAAx] lt r j) :
    Γ ⊢[PRAAx] recode (cell A r j) ≐ qzero := by
  have row : Γ ⊢[PRAAx] lt r m ⟶ aboveRow A m r := by simpa [aboveZeros] using h.allE r
  have entry : Γ ⊢[PRAAx] lt j m ⟶ lt r j ⟶ recode (cell A r j) ≐ qzero := by
    simpa [aboveRow] using (Prf.impE row hr).allE j
  exact .impE (.impE entry hj) hrj

theorem zero_factor_product (A m w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m)
    (hZero : Γ ⊢[PRAAx] recode (cell A (digit m w j) j) ≐ qzero) : Γ ⊢[PRAAx] rawProduct A m w ≐ qzero := by
  have factor : Γ ⊢[PRAAx] inst2 (GaussianRationalFiniteProduct.recodeBody factorBody) j (factorData A m w) ≐ qzero := by
    rw [GaussianRationalFiniteProduct.recode_body_at]
    exact (recode_congr (GaussianScalarDeterminant.factor_body_at A m w j)).eqTrans hZero
  have absorbed := GaussianRationalProductAlgebra.product_zero_at (GaussianRationalFiniteProduct.recodeBody factorBody)
    m j (factorData A m w) hj factor
  exact (GaussianRationalFiniteProduct.product_recode factorBody m (factorData A m w)).eqSymm.eqTrans absorbed

theorem other_word_product_zero (A m w : PTm n) (h : Γ ⊢[PRAAx] triangular A m)
    (hw : Γ ⊢[PRAAx] lt w (horizon m)) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hne : Γ ⊢[PRAAx] neg (w ≐ identityWord m)) : Γ ⊢[PRAAx] rawProduct A m w ≐ qzero := by
  refine .orE h ?_ ?_
  · have found := excess_found (Γ := belowZeros A m :: Γ) m w hw.wk hp.wk hne.wk
    exact zero_factor_product A m w (excessIndex m w) (.andE₁ found)
      (below_at A m (digit m w (excessIndex m w)) (excessIndex m w) Prf.hyp0
        (Foundations.RuntimePermutationWords.digit_bound _ _ _ (.andE₁ found)) (.andE₁ found) (.andE₂ found))
  · have found := deficit_found (Γ := aboveZeros A m :: Γ) m w hw.wk hp.wk hne.wk
    exact zero_factor_product A m w (deficitIndex m w) (.andE₁ found)
      (above_at A m (digit m w (deficitIndex m w)) (deficitIndex m w) Prf.hyp0
        (Foundations.RuntimePermutationWords.digit_bound _ _ _ (.andE₁ found)) (.andE₁ found) (.andE₂ found))

theorem identity_product (A m : PTm n) : Γ ⊢[PRAAx] rawProduct A m (identityWord m) ≐ diagonalProduct A m := by
  refine GaussianRationalFiniteProduct.product_congr_bounded factorBody diagonalBody m (factorData A m (identityWord m)) A (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have actual := (GaussianScalarDeterminant.factor_body_at (Γ := Δ) (Syn.shift A) (Syn.shift m) (identityWord (Syn.shift m)) (var 0)).eqTrans
    (entry_congr (entry_congr (.eqRefl (Syn.shift A)) (identity_digit _ _ Prf.hyp0)) (.eqRefl (var 0)))
  simpa only [Δ,Syn.shift,GaussianScalarDeterminant.subst_factorData,GaussianScalarIdentityDeterminant.subst_identityWord,diagonal_body_at,cell] using actual
theorem diagonal_canonical (A m : PTm n) : Γ ⊢[PRAAx] canonical (diagonalProduct A m) := GaussianRationalFiniteProduct.product_canonical _ _ _
theorem selected_term (A m r : PTm n) (he : Γ ⊢[PRAAx] GaussianPolynomialDeterminant.wordCode m r ≐ identityWord m) :
    Γ ⊢[PRAAx] signedTerm A m r ≐ diagonalProduct A m :=
  (qmul_congr (GaussianDeterminantSignTransport.sign_congr (.eqRefl m) he)
    (GaussianRationalFiniteProduct.product_index_congr factorBody (.eqRefl m)
      (congrPairT (.eqRefl A) (congrPairT (.eqRefl m) he)))).eqTrans
    ((qmul_congr (identity_sign m) (identity_product A m)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (diagonal_canonical A m))))
theorem other_term (A m r : PTm n) (h : Γ ⊢[PRAAx] triangular A m)
    (hr : Γ ⊢[PRAAx] lt r (count m)) (hne : Γ ⊢[PRAAx] neg (r ≐ identityRank m)) :
    Γ ⊢[PRAAx] signedTerm A m r ≐ qzero := by
  have wordNe : Γ ⊢[PRAAx] neg (GaussianPolynomialDeterminant.wordCode m r ≐ identityWord m) := by
    refine .impI (.impE hne.wk ?_)
    exact Foundations.RuntimePermutationWords.retained_position_unique m r (identityRank m) hr.wk (identity_rank_bound m).wk
      (Prf.hyp0.eqTrans (identity_rank_word m).wk.eqSymm)
  have valid := (Foundations.RuntimePermutationWords.checker_reflection m (GaussianPolynomialDeterminant.wordCode m r)).iffMpr (retained_valid m r hr)
  exact (qmul_congr (.eqRefl _) (other_word_product_zero A m _ h (retained_bound m r hr) valid wordNe)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem triangular_det (A m : PTm n) (h : Γ ⊢[PRAAx] triangular A m) :
    Γ ⊢[PRAAx] scalarDet A m ≐ diagonalProduct A m := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] triangular (Syn.shift A) (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual signedBody
      GaussianRationalMonicReconstruction.spikeBody (count m) (pairT A m)
      (GaussianRationalMonicReconstruction.spikeData (identityRank m) (diagonalProduct A m)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (count m)) :: Γ.map Fm.shift
    have rr : Δ ⊢[PRAAx] lt (var 0) (count (Syn.shift m)) := by
      simpa only [Δ,Syn.shift,Foundations.RuntimePermutationWords.subst_count] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have e : Δ ⊢[PRAAx] signedTerm (Syn.shift A) (Syn.shift m) (var 0) ≐
        GaussianRationalMonicReconstruction.spike (identityRank (Syn.shift m)) (diagonalProduct (Syn.shift A) (Syn.shift m)) (var 0) := by
      refine .orE (eq_or_ne (var 0) (identityRank (Syn.shift m))) ?_ ?_
      · have word : ((var 0) ≐ identityRank (Syn.shift m)) :: Δ ⊢[PRAAx]
            GaussianPolynomialDeterminant.wordCode (Syn.shift m) (var 0) ≐ identityWord (Syn.shift m) :=
          (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (identity_rank_word (Syn.shift m))
        exact (selected_term _ _ _ word).eqTrans (GaussianRationalMonicReconstruction.spike_hit _ _ _ Prf.hyp0).eqSymm
      · exact (other_term _ _ _ hs.wk.wk rr.wk Prf.hyp0).eqTrans
          (GaussianRationalMonicReconstruction.spike_miss _ _ _ Prf.hyp0).eqSymm
    have actual := (GaussianScalarDeterminant.signed_body_at (Γ := Δ) (Syn.shift A) (Syn.shift m) (var 0)).eqTrans
      (e.eqTrans (GaussianRationalMonicReconstruction.spike_body_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,subst_diagonalProduct,GaussianScalarIdentityDeterminant.subst_identityRank,subst_pairT,
      GaussianRationalMonicReconstruction.subst_spikeData] using actual
  exact (GaussianScalarDeterminant.scalar_leibniz A m).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      ((GaussianRationalMonicReconstruction.spike_sum _ _ _ (diagonal_canonical A m)).eqTrans
        (GaussianRationalMonicReconstruction.active_on _ _ _ (identity_rank_bound m))))

theorem upper_triangular_det (A m : PTm n) (h : Γ ⊢[PRAAx] belowZeros A m) :
    Γ ⊢[PRAAx] scalarDet A m ≐ diagonalProduct A m := triangular_det A m (.orI₁ h)
theorem lower_triangular_det (A m : PTm n) (h : Γ ⊢[PRAAx] aboveZeros A m) :
    Γ ⊢[PRAAx] scalarDet A m ≐ diagonalProduct A m := triangular_det A m (.orI₂ h)

def diagonalOnes (A m : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  recode (cell (Syn.shift A) (var 0) (var 0)) ≐ qone)
@[simp] theorem subst_diagonalOnes {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    (diagonalOnes A m).subst σ = diagonalOnes (Syn.subst σ A) (Syn.subst σ m) := by
  simp [diagonalOnes,Syn.subst_shift,Syn.shift_subst]
theorem diagonal_unit_product (A m : PTm n) (h : Γ ⊢[PRAAx] diagonalOnes A m) :
    Γ ⊢[PRAAx] diagonalProduct A m ≐ qone := by
  refine (GaussianRationalFiniteProduct.product_recode diagonalBody m A).eqSymm.eqTrans
    (GaussianRationalProductAlgebra.product_one_of_terms (GaussianRationalFiniteProduct.recodeBody diagonalBody) m A ?_)
  refine .allI (.impI ?_)
  rw [GaussianRationalFiniteProduct.recode_body_at,diagonal_body_at]
  exact .impE h.allOpen.wk Prf.hyp0
theorem unit_triangular_det (A m : PTm n) (h : Γ ⊢[PRAAx] triangular A m) (hOne : Γ ⊢[PRAAx] diagonalOnes A m) :
    Γ ⊢[PRAAx] scalarDet A m ≐ qone := (triangular_det A m h).eqTrans (diagonal_unit_product A m hOne)

def output (A m : PTm n) : PTm n := pairT A (pairT (scalarDet A m) (diagonalProduct A m))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (A m : PTm n) : PTm n := app outputF ![A,m]
def fields (p : PTm n) : Fin 3 → PTm n := ![fstT p,fstT (sndT p),sndT (sndT p)]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    Syn.subst σ (output A m) = output (Syn.subst σ A) (Syn.subst σ m) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    Syn.subst σ (run A m) = run (Syn.subst σ A) (Syn.subst σ m) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 3) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (A m : PTm n) : Γ ⊢[PRAAx] run A m ≐ output A m := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![A,m]
theorem returned_fields (A m : PTm n) (i : Fin 3) : Γ ⊢[PRAAx]
    fields (run A m) i ≐ ![A,scalarDet A m,diagonalProduct A m] i := by
  have e0 := program_at (Γ := Γ) A m
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrSnd e1).eqTrans (snd_pair _ _)
theorem returned_equality (A m : PTm n) (h : Γ ⊢[PRAAx] triangular A m) : Γ ⊢[PRAAx]
    fields (run A m) 1 ≐ fields (run A m) 2 :=
  (returned_fields A m 1).eqTrans ((triangular_det A m h).eqTrans (returned_fields A m 2).eqSymm)
theorem returned_unit (A m : PTm n) (h : Γ ⊢[PRAAx] triangular A m) (hOne : Γ ⊢[PRAAx] diagonalOnes A m) : Γ ⊢[PRAAx]
    fields (run A m) 1 ≐ qone := (returned_fields A m 1).eqTrans (unit_triangular_det A m h hOne)

theorem actual_excess_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (var 0)) ⟶ permutationBit (var 0) (var 1) ≐ one ⟶ neg (var 1 ≐ identityWord (var 0)) ⟶
      lt (excessIndex (var 0) (var 1)) (var 0) ⋏
        lt (excessIndex (var 0) (var 1)) (digit (var 0) (var 1) (excessIndex (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (.impI (excess_found _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_deficit_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (var 0)) ⟶ permutationBit (var 0) (var 1) ≐ one ⟶ neg (var 1 ≐ identityWord (var 0)) ⟶
      lt (deficitIndex (var 0) (var 1)) (var 0) ⋏
        lt (digit (var 0) (var 1) (deficitIndex (var 0) (var 1))) (deficitIndex (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (deficit_found _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_upper_triangular_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (belowZeros (var 0) (var 1) ⟶ scalarDet (var 0) (var 1) ≐ diagonalProduct (var 0) (var 1)) :=
  closeUniv 2 (.impI (upper_triangular_det _ _ Prf.hyp0))
theorem actual_lower_triangular_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (aboveZeros (var 0) (var 1) ⟶ scalarDet (var 0) (var 1) ≐ diagonalProduct (var 0) (var 1)) :=
  closeUniv 2 (.impI (lower_triangular_det _ _ Prf.hyp0))
theorem actual_triangular_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (triangular (var 0) (var 1) ⟶ scalarDet (var 0) (var 1) ≐ diagonalProduct (var 0) (var 1)) :=
  closeUniv 2 (.impI (triangular_det _ _ Prf.hyp0))
theorem actual_unit_triangular_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (triangular (var 0) (var 1) ⟶ diagonalOnes (var 0) (var 1) ⟶ scalarDet (var 0) (var 1) ≐ qone) :=
  closeUniv 2 (.impI (.impI (unit_triangular_det _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (triangular (var 0) (var 1) ⟶ fields (run (var 0) (var 1)) 1 ≐ fields (run (var 0) (var 1)) 2) :=
  closeUniv 2 (.impI (returned_equality _ _ Prf.hyp0))
theorem actual_returned_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (triangular (var 0) (var 1) ⟶ diagonalOnes (var 0) (var 1) ⟶ fields (run (var 0) (var 1)) 1 ≐ qone) :=
  closeUniv 2 (.impI (.impI (returned_unit _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianScalarTriangularDeterminant
