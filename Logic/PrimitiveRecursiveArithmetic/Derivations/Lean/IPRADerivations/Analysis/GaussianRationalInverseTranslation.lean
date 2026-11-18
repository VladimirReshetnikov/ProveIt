import IPRADerivations.Analysis.GaussianInverseBinomialRows

/-!
# The literal inverse-binomial identity for the actual translated polynomial

For the actual translated coefficient list B, the sum is the original
finite source expression: choose(k+r,k) B_(k+r) (-z)^r, for 0<=r<=N-k.
The guarded Pascal row is bound to these actual B entries and ordinary
binomial coefficients on their proved range. The original coefficient is
canonically recoded, so no canonical-input assumption or false raw-code
equality is needed. All lists, degrees, indices and query points are
numerical inputs of the actual PR4 output program.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalInverseTranslation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalNaturalScale (natScale natScale_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sourceTerm (B N z k r : PTm n) : PTm n := natScale (binom (k+r) k)
  (qmul (entry B (PTm.monus N (k+r))) (power (qnegative z) r))
def data (B N z k : PTm n) : PTm n := pairT B (pairT N (pairT z k))
def sourceBody : PTm 2 := sourceTerm (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def sourceSum (B N z k : PTm n) : PTm n := GaussianRationalFiniteSum.sum sourceBody
  (succ (PTm.monus N k)) (data B N z k)

@[simp] theorem subst_sourceTerm {m : ℕ} (σ : Fin n → PTm m) (B N z k r : PTm n) :
    Syn.subst σ (sourceTerm B N z k r) = sourceTerm (Syn.subst σ B) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ k) (Syn.subst σ r) := by simp [sourceTerm]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (B N z k : PTm n) :
    Syn.subst σ (data B N z k) = data (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ k) := by simp [data]
@[simp] theorem subst_sourceSum {m : ℕ} (σ : Fin n → PTm m) (B N z k : PTm n) :
    Syn.subst σ (sourceSum B N z k) = sourceSum (Syn.subst σ B) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ k) := by simp [sourceSum]

theorem source_term_congr {B B' N N' z z' k k' r r' : PTm n}
    (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N') (hz : Γ ⊢[PRAAx] z ≐ z')
    (hk : Γ ⊢[PRAAx] k ≐ k') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    sourceTerm B N z k r ≐ sourceTerm B' N' z' k' r' :=
  natScale_congr (congrBinom (congrAdd hk hr) hk)
    (qmul_congr (entry_congr hB (congrMonus hN (congrAdd hk hr)))
      (congrAp2 powerF hr (GaussianInverseBinomialRows.negative_congr hz)))

theorem source_body_at (B N z k r : PTm n) : Γ ⊢[PRAAx]
    inst2 sourceBody r (data B N z k) ≐ sourceTerm B N z k r := by
  have tail := snd_pair (Γ := Γ) B (pairT N (pairT z k))
  have nt := (congrSnd tail).eqTrans (snd_pair N (pairT z k))
  have eqs := source_term_congr (fst_pair B (pairT N (pairT z k)))
    ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrFst nt).eqTrans (fst_pair _ _)) ((congrSnd nt).eqTrans (snd_pair _ _)) (.eqRefl r)
  simpa only [sourceBody,inst2,subst_sourceTerm,subst_fstT,subst_sndT,Syn.subst_var,data,
    Matrix.cons_val_zero,Matrix.cons_val_one] using eqs

theorem binomial_on_offset (k r : PTm n) : Γ ⊢[PRAAx] gb (k+r) k ≐ binom (k+r) k :=
  (congrMul (Combinatorics.Stirling.gle_of_le (le_add_right k r)) (.eqRefl _)).eqTrans (one_mul _)

theorem offset_bound (N k r : PTm n) (hk : Γ ⊢[PRAAx] le k N)
    (hr : Γ ⊢[PRAAx] le r (PTm.monus N k)) : Γ ⊢[PRAAx] le (k+r) N :=
  le_congr (.eqRefl _) (eq_add_of_le hk).eqSymm (add_le_add₂ (le_refl k) hr)

theorem actual_term_binding (C N z k r : PTm n) (hi : Γ ⊢[PRAAx] le (k+r) N) : Γ ⊢[PRAAx]
    GaussianInverseBinomialRows.term C N z zero k r ≐
      sourceTerm (GaussianRationalTranslation.translated C N z) N z k r := by
  have coefficient := (GaussianInverseBinomialRows.b_congr (.eqRefl C) (.eqRefl N) (.eqRefl z)
    (by ipra_ring : Γ ⊢[PRAAx] zero+k+r ≐ k+r)).eqTrans
      (GaussianTranslationCoefficientValues.translated_coefficient_at C N z (k+r) hi)
  exact natScale_congr (binomial_on_offset k r) (qmul_congr coefficient (.eqRefl _))

/-- Every bounded row term is bound to the actual produced B entry. -/
theorem actual_sum_binding (C N z k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    GaussianInverseBinomialRows.R C N z zero k ≐
      sourceSum (GaussianRationalTranslation.translated C N z) N z k := by
  have count := GaussianRationalFiniteSum.sum_index_congr GaussianInverseBinomialRows.termBody
    (Γ := Γ) (x := GaussianInverseBinomialRows.data C N z zero k)
    (y := GaussianInverseBinomialRows.data C N z zero k)
    (congrSucc (congrMonus (.eqRefl N) (zero_add k))) (.eqRefl _)
  apply count.eqTrans
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have hks : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hk.shift
  have hr : (lt (var 0) (Syn.shift (succ (PTm.monus N k))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (PTm.monus (Syn.shift N) (Syn.shift k)) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (by
      simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,PTm.subst_monus,lt,le] using Prf.hyp0)
  have actual := actual_term_binding (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift k) (var 0)
    (offset_bound _ _ _ hks.wk hr)
  simpa only [Syn.shift,GaussianInverseBinomialRows.subst_data,subst_data,
    GaussianRationalTranslation.subst_translated,ConciseIPRA.PTm.subst_zero] using
    (GaussianInverseBinomialRows.term_at (Syn.shift C) (Syn.shift N) (Syn.shift z) zero (Syn.shift k) (var 0)).eqTrans
      (actual.eqTrans (source_body_at (GaussianRationalTranslation.translated (Syn.shift C) (Syn.shift N) (Syn.shift z))
        (Syn.shift N) (Syn.shift z) (Syn.shift k) (var 0)).eqSymm)

/-- The literal source inverse-translation sum, with ordinary binomial
coefficients and actual B entries, from original length alone. -/
theorem inverse_binomial_translation (C N z k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    recode (entry C (PTm.monus N k)) ≐ sourceSum (GaussianRationalTranslation.translated C N z) N z k :=
  (GaussianTranslationCoefficientValues.original_coefficient C N z k).eqSymm.eqTrans
    ((GaussianInverseBinomialRows.inverse_row C N z zero k hLen (zero_le N)
      (le_congr (.eqRefl _) (monus_zero N).eqSymm hk)).eqTrans (actual_sum_binding C N z k hk))

theorem canonical_inverse_binomial_translation (C N z k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] le k N)
    (hCanonical : Γ ⊢[PRAAx] canonical (entry C (PTm.monus N k))) : Γ ⊢[PRAAx]
    entry C (PTm.monus N k) ≐ sourceSum (GaussianRationalTranslation.translated C N z) N z k :=
  (GaussianTranslatedNonconstant.recode_eq _ hCanonical).eqSymm.eqTrans
    (inverse_binomial_translation C N z k hLen hk)

def output (C N z k : PTm n) : PTm n := pairT (recode (entry C (PTm.monus N k)))
  (pairT (sourceSum (GaussianRationalTranslation.translated C N z) N z k)
    (GaussianRationalTranslation.translated C N z))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N z k : PTm n) : PTm n := PTm.app outputF ![C,N,z,k]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N z k : PTm n) :
    Syn.subst σ (output C N z k) = output (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ k) := by simp [output]
theorem program_at (C N z k : PTm n) : Γ ⊢[PRAAx] run C N z k ≐ output C N z k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,z,k]
theorem returned_original (C N z k : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N z k) ≐ recode (entry C (PTm.monus N k)) :=
  (congrFst (program_at C N z k)).eqTrans (fst_pair _ _)
theorem returned_sum (C N z k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C N z k)) ≐ sourceSum (GaussianRationalTranslation.translated C N z) N z k :=
  ((congrFst (congrSnd (program_at C N z k))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_identity (C N z k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] fstT (run C N z k) ≐ fstT (sndT (run C N z k)) :=
  (returned_original C N z k).eqTrans ((inverse_binomial_translation C N z k hLen hk).eqTrans
    (returned_sum C N z k).eqSymm)

theorem inverse_binomial_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶
      recode (entry (var 0) (PTm.monus (var 1) (var 3))) ≐
        sourceSum (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (inverse_binomial_translation _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem inverse_translation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem returned_inverse_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (returned_identity _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalInverseTranslation
