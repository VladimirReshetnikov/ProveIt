import IPRADerivations.Analysis.RationalPolynomialDeterminantTermsGaussianEmbedding
import IPRADerivations.Analysis.GaussianRationalPolynomialPowers
import IPRADerivations.Analysis.RationalScalarPowerGaussianEmbedding

/-!
# Actual powers of original rational coefficient lists

Reuse the original rational product stage on the same numerical constant-cell
table as the Gaussian power program. The true product recurrence and a genuine
guarded QF induction derive evaluation as the original scalar power. No power,
coefficient, evaluation or global stage law is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPolynomialGaussianEmbedding (evaluate horner hornerF horner_zero horner_succ embed_congr)
open RationalPolynomialDeterminantTermsGaussianEmbedding (stage stage_zero stage_succ stage_length product_congr)
open RationalPolynomialProductGaussianEmbedding (product product_evaluation)
open GaussianRationalPolynomialPowers (table factor_original)
open RationalGaussianEmbedding (embed scalarOne embed_one embed_zero embed_add embed_multiply)
open GaussianRationalHorner (qzero qmul qadd)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qmul_zero_left qzero_add)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerPrefix (C N K j : PTm n) : PTm n := stage (table C K) K N zero j
def power (C N K : PTm n) : PTm n := powerPrefix C N K K
@[simp] theorem subst_powerPrefix {l : ℕ} (σ : Fin n → PTm l) (C N K j : PTm n) :
    Syn.subst σ (powerPrefix C N K j) = powerPrefix (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) := by simp [powerPrefix]
@[simp] theorem subst_power {l : ℕ} (σ : Fin n → PTm l) (C N K : PTm n) :
    Syn.subst σ (power C N K) = power (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) := by simp [power]

theorem prefix_zero (C N K : PTm n) : Γ ⊢[PRAAx] powerPrefix C N K zero ≐ singleton scalarOne := stage_zero _ _ _ _
theorem prefix_succ (C N K j : PTm n) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    powerPrefix C N K (succ j) ≐ product (powerPrefix C N K j) C (j*N) N :=
  (stage_succ _ _ _ _ _).eqTrans (product_congr (.eqRefl _) (factor_original C K j hj) (.eqRefl _) (.eqRefl _))
theorem prefix_length (C N K j : PTm n) : Γ ⊢[PRAAx] length (powerPrefix C N K j) ≐ succ (j*N) := stage_length _ _ _ _ _
theorem power_length (C N K : PTm n) : Γ ⊢[PRAAx] length (power C N K) ≐ succ (K*N) := prefix_length _ _ _ _

theorem evaluation_congr {C D z w : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hz : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate D w := congrAp3 hornerF (congrFst hC) hC hz

theorem singleton_evaluation (z : PTm n) : Γ ⊢[PRAAx] embed (evaluate (singleton scalarOne) z) ≐ qone := by
  have atOne : Γ ⊢[PRAAx] embed (horner (singleton scalarOne) z one) ≐ qone :=
    (embed_congr (horner_succ _ _ zero)).eqTrans ((embed_add _ _).eqTrans
      ((qadd_congr ((embed_multiply _ _).eqTrans
        ((qmul_congr ((embed_congr (horner_zero _ _)).eqTrans embed_zero) (.eqRefl _)).eqTrans (qmul_zero_left _)))
        ((embed_congr (singleton_lookup _)).eqTrans embed_one)).eqTrans (qzero_add _ GaussianRationalSyntheticDivision.qone_canonical)))
  exact (embed_congr (congrAp3 hornerF (singleton_length _) (.eqRefl _) (.eqRefl _))).eqTrans atOne

def evaluationLaw (C N K z j : PTm n) : Fm PTm n := le j K ⟶
  embed (evaluate (powerPrefix C N K j) z) ≐ GaussianRationalReciprocal.power (embed (evaluate C z)) j
@[simp] theorem subst_evaluationLaw {l : ℕ} (σ : Fin n → PTm l) (C N K z j : PTm n) :
    (evaluationLaw C N K z j).subst σ = evaluationLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ z) (Syn.subst σ j) := by simp [evaluationLaw]

theorem prefix_evaluation_embedding (C N K z j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] embed (evaluate (powerPrefix C N K j) z) ≐ GaussianRationalReciprocal.power (embed (evaluate C z)) j := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((embed_congr (evaluation_congr (prefix_zero _ _ _) (.eqRefl _))).eqTrans
        ((singleton_evaluation _).eqTrans (GaussianRationalReciprocal.power_zero _).eqSymm))
    · simp only [subst_evaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let a := Syn.shift C
      let b := Syn.shift N
      let c := Syn.shift K
      let x := Syn.shift z
      let Δ := le (succ (var 0)) c :: evaluationLaw a b c x (var 0) :: Γ.map Fm.shift
      have jj : Δ ⊢[PRAAx] lt (var 0) c := Prf.hyp0
      have ih : Δ ⊢[PRAAx] embed (evaluate (powerPrefix a b c (var 0)) x) ≐
          GaussianRationalReciprocal.power (embed (evaluate a x)) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) jj)
      exact (embed_congr (evaluation_congr (prefix_succ a b c (var 0) jj) (.eqRefl _))).eqTrans
        ((embed_congr (product_evaluation _ _ _ _ _ (prefix_length a b c (var 0)) cs.wk.wk)).eqTrans
          ((embed_multiply _ _).eqTrans ((qmul_congr ih (.eqRefl _)).eqTrans (GaussianRationalReciprocal.power_succ _ _).eqSymm)))
  have gate : Γ ⊢[PRAAx] evaluationLaw C N K z j := by
    simpa only [subst_evaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

theorem prefix_evaluation (C N K z j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    evaluate (powerPrefix C N K j) z ≐ RationalScalarPowerGaussianEmbedding.power (evaluate C z) j :=
  RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _)
    (RationalScalarPowerGaussianEmbedding.power_canonical _ _) ((prefix_evaluation_embedding C N K z j hC hj).eqTrans
      (RationalScalarPowerGaussianEmbedding.power_embedding _ _).eqSymm)
theorem power_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (power C N K) z ≐ RationalScalarPowerGaussianEmbedding.power (evaluate C z) K :=
  prefix_evaluation _ _ _ _ _ hC (le_refl _)

def powerF : PR 3 := PTm.toPR (power (var 0) (var 1) (var 2))
def prefixF : PR 4 := PTm.toPR (powerPrefix (var 0) (var 1) (var 2) (var 3))
def run (C N K : PTm n) : PTm n := app powerF ![C,N,K]
def prefixRun (C N K j : PTm n) : PTm n := app prefixF ![C,N,K,j]
theorem program_at (C N K : PTm n) : Γ ⊢[PRAAx] run C N K ≐ power C N K := by
  simpa [run,powerF] using toPR_eq (Γ := Γ) (power (var 0) (var 1) (var 2) : PTm 3) ![C,N,K]
theorem prefix_program_at (C N K j : PTm n) : Γ ⊢[PRAAx] prefixRun C N K j ≐ powerPrefix C N K j := by
  simpa [prefixRun,prefixF] using toPR_eq (Γ := Γ) (powerPrefix (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,K,j]
theorem returned_length (C N K : PTm n) : Γ ⊢[PRAAx] length (run C N K) ≐ succ (K*N) :=
  (congrFst (program_at C N K)).eqTrans (power_length _ _ _)
theorem returned_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (run C N K) z ≐ RationalScalarPowerGaussianEmbedding.power (evaluate C z) K :=
  (evaluation_congr (program_at C N K) (.eqRefl _)).eqTrans (power_evaluation _ _ _ _ hC)

theorem actual_original_power_prefix_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ powerPrefix (var 0) (var 1) (var 2) (succ (var 3)) ≐
      product (powerPrefix (var 0) (var 1) (var 2) (var 3)) (var 0) (var 3*var 1) (var 1)) :=
  closeUniv 4 (.impI (prefix_succ _ _ _ _ Prf.hyp0))
theorem actual_original_polynomial_power_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (power (var 0) (var 1) (var 2)) ≐ succ (var 2*var 1)) := closeUniv 3 (power_length _ _ _)
theorem actual_original_power_prefix_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 4) (var 2) ⟶ evaluate (powerPrefix (var 0) (var 1) (var 2) (var 4)) (var 3) ≐
      RationalScalarPowerGaussianEmbedding.power (evaluate (var 0) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (prefix_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_polynomial_power_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (power (var 0) (var 1) (var 2)) (var 3) ≐
      RationalScalarPowerGaussianEmbedding.power (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (power_evaluation _ _ _ _ Prf.hyp0))
theorem actual_original_polynomial_power_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) ≐ power (var 0) (var 1) (var 2) ⋏
      prefixRun (var 0) (var 1) (var 2) (var 3) ≐ powerPrefix (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.andI (program_at _ _ _) (prefix_program_at _ _ _ _))
theorem actual_returned_original_power_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (run (var 0) (var 1) (var 2)) (var 3) ≐
      RationalScalarPowerGaussianEmbedding.power (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (returned_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialPowers
