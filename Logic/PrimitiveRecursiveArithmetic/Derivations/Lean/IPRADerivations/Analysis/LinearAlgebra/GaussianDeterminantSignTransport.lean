import IPRADerivations.Foundations.RuntimeAdjacentPermutationSwap
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantTerms
import IPRADerivations.Analysis.Polynomials.GaussianInverseBinomialRows
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientNormOrder
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual Gaussian sign transport for numerical permutation words

The numerical adjacent-swap inversion theorem determines the actual
Gaussian determinant signs: even is +1 and odd is -1. The same scalar
factor then gives two opposite signed products and a literal zero sum.
Retained-word validity is derived from the original rank bounds. No
determinant alternation, product reindexing or kernel law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDeterminantSignTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (canonical qzero qadd qmul canonical_unique represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric
  (qnegative qnegative_canonical qnegative_represents qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianInverseBinomialRows (negative_congr negative_product)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (signPoint sign_even sign_odd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Arbitrary raw inputs are compared with their actual canonical recode.
The literal double-negative identity with the original code requires its
canonical guard, as exposed separately below. -/
theorem negative_involution_recode (q : PTm n) : Γ ⊢[PRAAx]
    qnegative (qnegative q) ≐ GaussianTranslatedNonconstant.recode q := by
  apply canonical_unique _ _ (rawGaussian q) (rawDen q)
    (qnegative_canonical _) (GaussianTranslatedNonconstant.recode_canonical _) (raw_den_positive q)
    (hrv := GaussianTranslatedNonconstant.recode_represents _)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := qnegative_represents _ _ _ (qnegative_represents _ _ _ (raw_represents q)))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg] <;> ring

theorem negative_involution (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    qnegative (qnegative q) ≐ q :=
  (negative_involution_recode _).eqTrans (GaussianTranslatedNonconstant.recode_eq _ hq)

theorem sign_congr {m m' w w' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') : Γ ⊢[PRAAx] signPoint m w ≐ signPoint m' w' := by
  ipra_congr (signPoint (var 0) (var 1) : PTm 2) with [hm, hw]

theorem sign_flip (m w j : PTm n)
    (hPerm : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    signPoint m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) ≐ qnegative (signPoint m w) := by
  have hp := Foundations.RuntimeAdjacentPermutationSwap.parity_flip m w j hj
    (Foundations.RuntimeAdjacentPermutationSwap.adjacent_digits_different _ _ _ hPerm hj)
  refine .orE (Foundations.RuntimePermutationWords.parity_cases m w) ?_ ?_
  · have hn := hp.wk.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))
    exact (sign_odd _ _ hn).eqTrans (negative_congr (sign_even _ _ Prf.hyp0)).eqSymm
  · have hn := hp.wk.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _))
    exact (sign_even _ _ hn).eqTrans
      ((negative_involution qone qone_canonical).eqSymm.eqTrans (negative_congr (sign_odd _ _ Prf.hyp0)).eqSymm)

theorem retained_sign_flip (m j t : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    signPoint m (entry (Foundations.RuntimePermutationWords.words m)
      (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t)) ≐
        qnegative (signPoint m (entry (Foundations.RuntimePermutationWords.words m) t)) :=
  (sign_congr (.eqRefl _) (.andE₂ (Foundations.RuntimeAdjacentPermutationSwap.retained_transport _ _ _ ht hj))).eqTrans
    (sign_flip _ _ _ (Foundations.RuntimePermutationWords.retained_valid _ _ ht) hj)

theorem signed_scalar_flip (m w j u : PTm n)
    (hPerm : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    qmul (signPoint m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j)) u ≐
      qnegative (qmul (signPoint m w) u) :=
  (qmul_congr (sign_flip _ _ _ hPerm hj) (.eqRefl _)).eqTrans (negative_product _ _).eqSymm

theorem signed_scalar_cancel (m w j u : PTm n)
    (hPerm : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    qadd (qmul (signPoint m w) u)
      (qmul (signPoint m (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j)) u) ≐ qzero :=
  (qadd_congr (.eqRefl _) (signed_scalar_flip _ _ _ _ hPerm hj)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self _)

def oldSigned (m t u : PTm n) : PTm n := qmul (signPoint m (entry (Foundations.RuntimePermutationWords.words m) t)) u
def newSigned (m j t u : PTm n) : PTm n := qmul
  (signPoint m (entry (Foundations.RuntimePermutationWords.words m) (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t))) u
def pairSum (m j t u : PTm n) : PTm n := qadd (oldSigned m t u) (newSigned m j t u)
@[simp] theorem subst_oldSigned {l : ℕ} (σ : Fin n → PTm l) (m t u : PTm n) :
    Syn.subst σ (oldSigned m t u) = oldSigned (Syn.subst σ m) (Syn.subst σ t) (Syn.subst σ u) := by simp [oldSigned]
@[simp] theorem subst_newSigned {l : ℕ} (σ : Fin n → PTm l) (m j t u : PTm n) :
    Syn.subst σ (newSigned m j t u) = newSigned (Syn.subst σ m) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ u) := by simp [newSigned]
@[simp] theorem subst_pairSum {l : ℕ} (σ : Fin n → PTm l) (m j t u : PTm n) :
    Syn.subst σ (pairSum m j t u) = pairSum (Syn.subst σ m) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ u) := by simp [pairSum]
theorem old_signed_canonical (m t u : PTm n) : Γ ⊢[PRAAx] canonical (oldSigned m t u) :=
  GaussianRationalHorner.qmul_canonical _ _
theorem new_signed_canonical (m j t u : PTm n) : Γ ⊢[PRAAx] canonical (newSigned m j t u) :=
  GaussianRationalHorner.qmul_canonical _ _
theorem pair_sum_canonical (m j t u : PTm n) : Γ ⊢[PRAAx] canonical (pairSum m j t u) :=
  GaussianRationalHorner.qadd_canonical _ _
theorem retained_scalar_flip (m j t u : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    newSigned m j t u ≐ qnegative (oldSigned m t u) :=
  (qmul_congr (retained_sign_flip _ _ _ ht hj) (.eqRefl _)).eqTrans (negative_product _ _).eqSymm
theorem retained_scalar_cancel (m j t u : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] pairSum m j t u ≐ qzero :=
  (qadd_congr (.eqRefl _) (retained_scalar_flip _ _ _ _ ht hj)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

/-- The retained program binds the same actual rank and original word
list used by the numerical swap theorem, together with the two signed
scalar products and their computed sum. The scalar may be raw or zero. -/
def output (m j t u : PTm n) : PTm n := pairT (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t)
  (pairT (entry (Foundations.RuntimePermutationWords.words m) (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t))
    (pairT (oldSigned m t u) (pairT (newSigned m j t u) (pairSum m j t u))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (m j t u : PTm n) : PTm n := app outputF ![m,j,t,u]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (m j t u : PTm n) :
    Syn.subst σ (output m j t u) = output (Syn.subst σ m) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ u) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (m j t u : PTm n) :
    Syn.subst σ (run m j t u) = run (Syn.subst σ m) (Syn.subst σ j) (Syn.subst σ t) (Syn.subst σ u) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (m j t u : PTm n) : Γ ⊢[PRAAx] run m j t u ≐ output m j t u := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3)) ![m,j,t,u]
theorem returned_rank (m j t u : PTm n) : Γ ⊢[PRAAx]
    fstT (run m j t u) ≐ Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_word (m j t u : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run m j t u)) ≐ entry (Foundations.RuntimePermutationWords.words m)
      (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t) :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_old_signed (m j t u : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run m j t u))) ≐ oldSigned m t u :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_new_signed (m j t u : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run m j t u)))) ≐ newSigned m j t u :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sum (m j t u : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run m j t u)))) ≐ pairSum m j t u :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_sum_zero (m j t u : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run m j t u)))) ≐ qzero :=
  (returned_sum _ _ _ _).eqTrans (retained_scalar_cancel _ _ _ _ ht hj)

/-! Every dimension, original word, retained rank, swap position and scalar
is numerically bound in these ordinary PRA source endpoints. -/
theorem actual_raw_double_negative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qnegative (qnegative (var 0)) ≐ GaussianTranslatedNonconstant.recode (var 0)) :=
  closeUniv 1 (negative_involution_recode _)
theorem actual_canonical_double_negative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (canonical (var 0) ⟶ qnegative (qnegative (var 0)) ≐ var 0) :=
  closeUniv 1 (.impI (negative_involution _ Prf.hyp0))
theorem actual_word_sign_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Foundations.RuntimePermutationWords.permutation (var 0) (var 1) ⟶ lt (succ (var 2)) (var 0) ⟶
      signPoint (var 0) (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 0) (var 1) (var 2)) ≐
        qnegative (signPoint (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (sign_flip _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_retained_sign_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (Foundations.RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      signPoint (var 0) (entry (Foundations.RuntimePermutationWords.words (var 0))
        (Foundations.RuntimeAdjacentPermutationSwap.rankSwap (var 0) (var 1) (var 2))) ≐
          qnegative (signPoint (var 0) (entry (Foundations.RuntimePermutationWords.words (var 0)) (var 2)))) :=
  closeUniv 3 (.impI (.impI (retained_sign_flip _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_signed_scalar_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Foundations.RuntimePermutationWords.permutation (var 0) (var 1) ⟶ lt (succ (var 2)) (var 0) ⟶
      qmul (signPoint (var 0) (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 0) (var 1) (var 2))) (var 3) ≐
        qnegative (qmul (signPoint (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (signed_scalar_flip _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_signed_scalar_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Foundations.RuntimePermutationWords.permutation (var 0) (var 1) ⟶ lt (succ (var 2)) (var 0) ⟶
      qadd (qmul (signPoint (var 0) (var 1)) (var 3))
        (qmul (signPoint (var 0) (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 0) (var 1) (var 2))) (var 3)) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (signed_scalar_cancel _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_retained_scalar_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (Foundations.RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      pairSum (var 0) (var 1) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (retained_scalar_cancel _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_sign_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_zero_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (Foundations.RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (returned_sum_zero _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianDeterminantSignTransport
