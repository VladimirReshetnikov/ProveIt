import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalConjugation
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassFactors
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows

/-!
# Conjugation of the original finite Gamma products

The SAME polynomial head and literal factor-by-factor Weierstrass prefix
commute with conjugation at every numerical index and Taylor cutoff.
The actual source disk is preserved. Named C7/Gamma transport is separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalConjugation (point point_congr point_add point_mul point_one point_negative of_gaussian point_scalar_sum)
open GaussianRationalReciprocal (conjugate)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaWeierstrassFactors (localArgument literalPrefix)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem native_disk (z R : PTm n) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (conjugate z) R :=
  le_congr (GaussianRationalReciprocal.norm_conjugate z).eqSymm (.eqRefl _) hz

theorem source_conjugate (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source (conjugate z) R B :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (native_disk z (R*B) h.andE₂.andE₂))

theorem head_factor (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    point (GaussianGammaEulerHead.factor i z B) ≐ GaussianGammaEulerHead.factor i (conjugate z) B :=
  (point_add _ _).eqTrans (qadd_congr point_one (of_gaussian z (B*succ i)
    (GaussianRationalHorner.positive_product _ _ hB (zero_lt_succ i))))

def headLaw (z B N : PTm n) : Fm PTm n :=
  point (GaussianGammaEulerHead.head z B N) ≐ GaussianGammaEulerHead.head (conjugate z) B N
@[simp] theorem subst_headLaw {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    (headLaw z B N).subst σ = headLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [headLaw]
theorem head_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] headLaw z B zero :=
  (point_congr (GaussianGammaEulerHead.head_zero z B hB)).eqTrans
    ((of_gaussian z B hB).eqTrans (GaussianGammaEulerHead.head_zero (conjugate z) B hB).eqSymm)
theorem head_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (ih : Γ ⊢[PRAAx] headLaw z B N) : Γ ⊢[PRAAx] headLaw z B (succ N) :=
  (point_congr (GaussianGammaEulerHead.head_succ z B N)).eqTrans ((point_mul _ _).eqTrans
    ((qmul_congr ih (head_factor N z B hB)).eqTrans (GaussianGammaEulerHead.head_succ (conjugate z) B N).eqSymm))

/-- Atomic QF induction follows the original finite polynomial program. -/
theorem head_conjugate (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] headLaw z B N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using head_zero (Γ := Γ) z B hB
    · simpa only [subst_headLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using head_step (Syn.shift z) (Syn.shift B) (var 0) bs.wk Prf.hyp0
  simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem returned_head_conjugate (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    point (GaussianGammaEulerHead.run z B N) ≐ GaussianGammaEulerHead.run (conjugate z) B N :=
  (point_congr (GaussianGammaEulerHead.program_at z B N)).eqTrans
    ((head_conjugate z B N hB).eqTrans (GaussianGammaEulerHead.program_at (conjugate z) B N).eqSymm)

theorem local_argument (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    point (localArgument i z B) ≐ localArgument i (conjugate z) B :=
  (point_negative _).eqTrans (GaussianInverseBinomialRows.negative_congr (of_gaussian z (B*succ i)
    (GaussianRationalHorner.positive_product _ _ hB (zero_lt_succ i))))

theorem literal_factor (i z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    point (GaussianGammaWeierstrassFactors.factor i z B K) ≐ GaussianGammaWeierstrassFactors.factor i (conjugate z) B K :=
  (point_mul _ _).eqTrans (qmul_congr (head_factor i z B hB)
    ((point_scalar_sum _ K).eqTrans (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (local_argument i z B hB))))

def prefixLaw (z B K N : PTm n) : Fm PTm n := point (literalPrefix z B K N) ≐ literalPrefix (conjugate z) B K N
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (z B K N : PTm n) :
    (prefixLaw z B K N).subst σ = prefixLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ N) := by simp [prefixLaw]
theorem prefix_zero (z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] prefixLaw z B K zero :=
  (point_congr (GaussianGammaWeierstrassFactors.literal_zero z B K hB)).eqTrans
    ((of_gaussian z B hB).eqTrans (GaussianGammaWeierstrassFactors.literal_zero (conjugate z) B K hB).eqSymm)
theorem prefix_step (z B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (ih : Γ ⊢[PRAAx] prefixLaw z B K N) : Γ ⊢[PRAAx] prefixLaw z B K (succ N) :=
  (point_congr (GaussianGammaWeierstrassFactors.literal_step z B K N)).eqTrans ((point_mul _ _).eqTrans
    ((qmul_congr ih (literal_factor N z B K hB)).eqTrans (GaussianGammaWeierstrassFactors.literal_step (conjugate z) B K N).eqSymm))

/-- The original factors are conjugated individually at the SAME actual
Taylor cutoff; no folded exponential product law is an input. -/
theorem literal_prefix_conjugate (z B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] prefixLaw z B K N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift z) (Syn.shift B) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) z B K hB
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using prefix_step (Syn.shift z) (Syn.shift B) (Syn.shift K) (var 0) bs.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def output (z B K N : PTm n) : PTm n := pairT (point (GaussianGammaEulerHead.head z B N))
  (pairT (GaussianGammaEulerHead.head (conjugate z) B N) (pairT (point (literalPrefix z B K N)) (literalPrefix (conjugate z) B K N)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z B K N : PTm n) : PTm n := PTm.app outputF ![z,B,K,N]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (z B K N : PTm n) :
    Syn.subst σ (output z B K N) = output (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (z B K N : PTm n) :
    Syn.subst σ (run z B K N) = run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (z B K N : PTm n) : Γ ⊢[PRAAx] run z B K N ≐ output z B K N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,B,K,N]
theorem returned_head (z B K N : PTm n) : Γ ⊢[PRAAx] fstT (run z B K N) ≐ point (GaussianGammaEulerHead.head z B N) :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (z B K N : PTm n) : Γ ⊢[PRAAx] sndT (run z B K N) ≐
    pairT (GaussianGammaEulerHead.head (conjugate z) B N) (pairT (point (literalPrefix z B K N)) (literalPrefix (conjugate z) B K N)) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_conjugate_head (z B K N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z B K N)) ≐ GaussianGammaEulerHead.head (conjugate z) B N :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_prefix_pair (z B K N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z B K N)) ≐
    pairT (point (literalPrefix z B K N)) (literalPrefix (conjugate z) B K N) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_prefix (z B K N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run z B K N))) ≐ point (literalPrefix z B K N) :=
  (congrFst (returned_prefix_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_prefix_conjugate (z B K N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run z B K N))) ≐ literalPrefix (conjugate z) B K N :=
  (congrSnd (returned_prefix_pair _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equalities (z B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    (fstT (run z B K N) ≐ fstT (sndT (run z B K N))) ⋏
      (fstT (sndT (sndT (run z B K N))) ≐ sndT (sndT (sndT (run z B K N)))) :=
  .andI ((returned_head _ _ _ _).eqTrans ((head_conjugate z B N hB).eqTrans (returned_conjugate_head _ _ _ _).eqSymm))
    ((returned_prefix _ _ _ _).eqTrans ((literal_prefix_conjugate z B K N hB).eqTrans (returned_prefix_conjugate _ _ _ _).eqSymm))

theorem original_gamma_source_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      GaussianGammaCanonicalExponent.source (conjugate (var 0)) (var 1) (var 2)) := closeUniv 3 (.impI (source_conjugate _ _ _ Prf.hyp0))
theorem original_finite_gamma_head_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ headLaw (var 0) (var 1) (var 2)) := closeUniv 3 (.impI (head_conjugate _ _ _ Prf.hyp0))
theorem original_returned_gamma_head_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ point (GaussianGammaEulerHead.run (var 0) (var 1) (var 2)) ≐
      GaussianGammaEulerHead.run (conjugate (var 0)) (var 1) (var 2)) := closeUniv 3 (.impI (returned_head_conjugate _ _ _ Prf.hyp0))
theorem original_gamma_local_argument_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ point (localArgument (var 0) (var 1) (var 2)) ≐ localArgument (var 0) (conjugate (var 1)) (var 2)) :=
  closeUniv 3 (.impI (local_argument _ _ _ Prf.hyp0))
theorem original_literal_gamma_factor_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ point (GaussianGammaWeierstrassFactors.factor (var 0) (var 1) (var 2) (var 3)) ≐
      GaussianGammaWeierstrassFactors.factor (var 0) (conjugate (var 1)) (var 2) (var 3)) := closeUniv 4 (.impI (literal_factor _ _ _ _ Prf.hyp0))
theorem original_literal_gamma_prefix_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ prefixLaw (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (.impI (literal_prefix_conjugate _ _ _ _ Prf.hyp0))
theorem actual_finite_gamma_conjugation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem original_returned_finite_gamma_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ⋏
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (returned_equalities _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteConjugation
