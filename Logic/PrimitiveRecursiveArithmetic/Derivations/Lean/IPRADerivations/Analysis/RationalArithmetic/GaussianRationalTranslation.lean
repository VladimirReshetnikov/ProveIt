import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTranslationStages
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTranslationAlgebra
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianBalancedRadiusSyntax
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual rational polynomial translation by repeated synthetic division

The produced list is in descending Horner order. Its coefficient at index
`h` is the actual remainder obtained after `N-h` successive divisions by
`X-z`. In particular its ascending coefficient `i` is the evaluation at z
of the actual stage-i quotient. A backwards-prefix QF induction proves
the original translation identity. No translated coefficient, division
identity or evaluation law is supplied by the caller. All degrees, list
codes, translation points and evaluation points remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalTranslation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical evaluate horner hornerF horner_canonical canonical_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone canonicalCoefficients qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (stage subst_stage)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientValue (C N z h : PTm n) : PTm n := evaluate (stage C N z (monus N h)) z
def data (C N z : PTm n) : PTm n := pairT C (pairT N z)
def coefficientBody : PTm 2 := coefficientValue (fstT (var 1)) (fstT (sndT (var 1)))
  (sndT (sndT (var 1))) (var 0)
def translated (C N z : PTm n) : PTm n := sequence coefficientBody (succ N) (data C N z)

@[simp] theorem subst_coefficientValue {m : ℕ} (σ : Fin n → PTm m) (C N z h : PTm n) :
    Syn.subst σ (coefficientValue C N z h) =
      coefficientValue (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ h) := by
  simp [coefficientValue]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (data C N z) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [data]
@[simp] theorem subst_translated {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (translated C N z) = translated (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by
  simp [translated]

theorem evaluate_congr {C D y z : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hy : Γ ⊢[PRAAx] y ≐ z) :
    Γ ⊢[PRAAx] evaluate C y ≐ evaluate D z :=
  congrAp3 hornerF (congrFst hC) hC hy

theorem stage_index_congr (C N z : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] stage C N z i ≐ stage C N z j := by
  ipra_congr (stage (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl C, .eqRefl N, .eqRefl z, h]

theorem coefficient_value_at (C N z h : PTm n) : Γ ⊢[PRAAx]
    inst2 coefficientBody h (data C N z) ≐ coefficientValue C N z h := by
  have hC : Γ ⊢[PRAAx] fstT (data C N z) ≐ C := fst_pair _ _
  have hN : Γ ⊢[PRAAx] fstT (sndT (data C N z)) ≐ N :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hz : Γ ⊢[PRAAx] sndT (sndT (data C N z)) ≐ z :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  ipra_congr (coefficientValue (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [hC, hN, hz, .eqRefl h] using [coefficientBody, inst2]

theorem translated_length (C N z : PTm n) : Γ ⊢[PRAAx] length (translated C N z) ≐ succ N :=
  sequence_length _ _ _

theorem translated_lookup (C N z h : PTm n) (hh : Γ ⊢[PRAAx] le h N) : Γ ⊢[PRAAx]
    entry (translated C N z) h ≐ coefficientValue C N z h :=
  (sequence_decode coefficientBody ((succ_monus_succ h N).eqTrans hh)).eqTrans (coefficient_value_at C N z h)

theorem translated_coefficient_canonical (C N z h : PTm n) (hh : Γ ⊢[PRAAx] le h N) :
    Γ ⊢[PRAAx] canonical (entry (translated C N z) h) :=
  canonical_congr (translated_lookup C N z h hh) (horner_canonical _ _ _)

theorem translated_canonical (C N z : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (translated C N z) := by
  refine .allI (.impI ?_)
  have hi : lt (var 0) (length (Syn.shift (translated C N z))) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (by
      simpa only [Syn.shift,subst_translated] using translated_length (Syn.shift C) (Syn.shift N) (Syn.shift z)) Prf.hyp0)
  simpa only [Syn.shift,subst_translated] using
    translated_coefficient_canonical (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0) hi

theorem constant_coefficient (C N z : PTm n) : Γ ⊢[PRAAx]
    entry (translated C N z) N ≐ evaluate C z :=
  (translated_lookup C N z N (le_refl _)).eqTrans
    (evaluate_congr ((stage_index_congr C N z (monus_self N)).eqTrans
      (GaussianRationalTranslationStages.stage_zero C N z)) (.eqRefl _))

theorem ascending_coefficient (C N z i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (translated C N z) N i ≐ evaluate (stage C N z i) z := by
  have reverse : Γ ⊢[PRAAx] monus N (monus N i) ≐ i :=
    (congrMonus (eq_add_of_le hi) (.eqRefl _)).eqTrans (add_monus _ _)
  have bound : Γ ⊢[PRAAx] le (monus N i) N :=
    le_of_eq_add ((eq_add_of_le hi).eqTrans (add_comm _ _))
  exact (translated_lookup C N z (monus N i) bound).eqTrans
    (evaluate_congr (stage_index_congr C N z reverse) (.eqRefl _))

theorem ascending_constant (C N z : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (translated C N z) N zero ≐ evaluate C z :=
  (ascending_coefficient C N z zero (zero_le _)).eqTrans
    (evaluate_congr (GaussianRationalTranslationStages.stage_zero C N z) (.eqRefl _))

theorem monic_leading (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    entry (translated C N z) zero ≐ qone :=
  (translated_lookup C N z zero (zero_le _)).eqTrans
    ((evaluate_congr (stage_index_congr C N z (monus_zero N)) (.eqRefl _)).eqTrans
      (GaussianRationalTranslationStages.terminal_monic_evaluation C N z z hLen hm))

/-- The initial translated Horner prefix is the actual constant terminal
quotient, evaluated at the shifted query. No canonical input is needed. -/
theorem backward_prefix_zero (C N z w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    horner (translated C N z) w (succ zero) ≐ evaluate (stage C N z (monus N zero)) (qadd z w) := by
  have atZero := translated_lookup (Γ := Γ) C N z zero (zero_le _)
  have outputCanonical : Γ ⊢[PRAAx] canonical (entry (translated C N z) zero) :=
    translated_coefficient_canonical C N z zero (zero_le _)
  have initial := (GaussianRationalHorner.horner_succ (Γ := Γ) (translated C N z) w zero).eqTrans
    ((qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero _ _) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left w)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ outputCanonical))
  exact initial.eqTrans (atZero.eqTrans
    ((evaluate_congr (stage_index_congr C N z (monus_zero N)) (.eqRefl _)).eqTrans
      ((GaussianRationalTranslationStages.terminal_evaluation C N z z (qadd z w) hLen).eqTrans
        (evaluate_congr (stage_index_congr C N z (monus_zero N)).eqSymm (.eqRefl _)))))

/-- One genuine backwards-prefix step, using the actual next synthetic
quotient and the actual shifted-query division identity. -/
theorem backward_prefix_step (C N z w k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hk : Γ ⊢[PRAAx] lt k N)
    (hIH : Γ ⊢[PRAAx] horner (translated C N z) w (succ k) ≐
      evaluate (stage C N z (monus N k)) (qadd z w)) : Γ ⊢[PRAAx]
    horner (translated C N z) w (succ (succ k)) ≐
      evaluate (stage C N z (monus N (succ k))) (qadd z w) := by
  have split : Γ ⊢[PRAAx] N ≐ k+succ (monus N (succ k)) :=
    (AnalyticNumberTheory.Totatives.split_lt hk).eqTrans (add_comm _ _)
  have hj : Γ ⊢[PRAAx] lt (monus N (succ k)) N :=
    le_congr (.eqRefl _) split.eqSymm (le_add_left (succ (monus N (succ k))) k)
  have reverse : Γ ⊢[PRAAx] succ (monus N (succ k)) ≐ monus N k :=
    (GaussianRationalTranslationStages.remaining_step N k hk).eqSymm
  have division := GaussianRationalTranslationStages.stage_division C N z (qadd z w)
    (monus N (succ k)) hLen hj
  have value : Γ ⊢[PRAAx] evaluate (stage C N z (monus N (succ k))) (qadd z w) ≐
      qadd (qmul (evaluate (stage C N z (monus N k)) (qadd z w)) w)
        (evaluate (stage C N z (monus N (succ k))) z) :=
    (division.eqTrans (GaussianRationalTranslationAlgebra.shifted_division_step z w _ _)).eqTrans
      (qadd_congr (qmul_congr (evaluate_congr (stage_index_congr C N z reverse) (.eqRefl _))
        (.eqRefl _)) (.eqRefl _))
  exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr hIH (.eqRefl _)) (translated_lookup C N z (succ k) hk)).eqTrans value.eqSymm)

def prefixLaw (C N z w k : PTm n) : Fm PTm n := le k N ⟶
  horner (translated C N z) w (succ k) ≐ evaluate (stage C N z (monus N k)) (qadd z w)

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C N z w k : PTm n) :
    (prefixLaw C N z w k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ k) := by simp [prefixLaw]

theorem backward_prefix (C N z w k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    horner (translated C N z) w (succ k) ≐ evaluate (stage C N z (monus N k)) (qadd z w) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (backward_prefix_zero C N z w hLen.wk)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
        simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
      have hi : (le (succ (var 0)) (Syn.shift N)) ::
          prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift w) (var 0) :: Γ.map Fm.shift
          ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      exact backward_prefix_step _ _ _ _ _ hs.wk.wk Prf.hyp0 (.impE Prf.hyp1 hi)
  have rule : Γ ⊢[PRAAx] prefixLaw C N z w k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-- The complete actual translation identity, including numerical degree
zero and independently normalized or noncanonical input coefficients. -/
theorem translation_evaluation (C N z w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (translated C N z) w ≐ evaluate C (qadd z w) :=
  (congrAp3 hornerF (translated_length C N z) (.eqRefl _) (.eqRefl _)).eqTrans
    ((backward_prefix C N z w N hLen (le_refl _)).eqTrans
      (evaluate_congr ((stage_index_congr C N z (monus_self N)).eqTrans
        (GaussianRationalTranslationStages.stage_zero C N z)) (.eqRefl _)))

/-! The actual fixed PR3 producer returns the constructed coefficient
list itself. Every field and evaluator below concerns that literal output. -/
def outputF : PR 3 := PTm.toPR (translated (var 0) (var 1) (var 2))

theorem program_at (C N z : PTm n) : Γ ⊢[PRAAx] ap3 outputF C N z ≐ translated C N z := by
  simpa [outputF,ap3] using toPR_eq (Γ := Γ) (translated (var 0) (var 1) (var 2) : PTm 3) ![C,N,z]

theorem returned_length (C N z : PTm n) : Γ ⊢[PRAAx] length (ap3 outputF C N z) ≐ succ N :=
  (congrFst (program_at C N z)).eqTrans (translated_length C N z)

theorem returned_canonical (C N z : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (ap3 outputF C N z) :=
  by
    have p := Prf.eqSubst (Γ := Γ) (canonicalCoefficients (var 0) : Fm PTm 1)
      ![translated C N z] ![ap3 outputF C N z]
      (fun i => by fin_cases i; exact (program_at C N z).eqSymm) (by simpa using translated_canonical C N z)
    simpa only [GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.subst_var,Matrix.cons_val_zero] using p

theorem returned_lookup (C N z h : PTm n) (hh : Γ ⊢[PRAAx] le h N) : Γ ⊢[PRAAx]
    entry (ap3 outputF C N z) h ≐ coefficientValue C N z h :=
  (entry_congr (program_at C N z) (.eqRefl _)).eqTrans (translated_lookup C N z h hh)

theorem returned_constant (C N z : PTm n) : Γ ⊢[PRAAx]
    entry (ap3 outputF C N z) N ≐ evaluate C z :=
  (entry_congr (program_at C N z) (.eqRefl _)).eqTrans (constant_coefficient C N z)

theorem returned_evaluation (C N z w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (ap3 outputF C N z) w ≐ evaluate C (qadd z w) :=
  (evaluate_congr (program_at C N z) (.eqRefl _)).eqTrans (translation_evaluation C N z w hLen)

theorem returned_monic (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    entry (ap3 outputF C N z) zero ≐ qone :=
  (entry_congr (program_at C N z) (.eqRefl _)).eqTrans (monic_leading C N z hLen hm)

theorem translation_structure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (translated (var 0) (var 1) (var 2)) ≐ succ (var 1)) ⋏
      (canonicalCoefficients (translated (var 0) (var 1) (var 2)) ⋏
        entry (translated (var 0) (var 1) (var 2)) (var 1) ≐ evaluate (var 0) (var 2))) :=
  closeUniv 3 (.andI (translated_length _ _ _) (.andI (translated_canonical _ _ _) (constant_coefficient _ _ _)))

theorem translation_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶
      GaussianBalancedRadiusSyntax.coefficient (translated (var 0) (var 1) (var 2)) (var 1) (var 3) ≐
        evaluate (stage (var 0) (var 1) (var 2) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (ascending_coefficient _ _ _ _ Prf.hyp0))

theorem translation_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 4) (var 1) ⟶
      horner (translated (var 0) (var 1) (var 2)) (var 3) (succ (var 4)) ≐
        evaluate (stage (var 0) (var 1) (var 2) (monus (var 1) (var 4))) (qadd (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (backward_prefix _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem translation_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (translated (var 0) (var 1) (var 2)) (var 3) ≐ evaluate (var 0) (qadd (var 2) (var 3))) :=
  closeUniv 4 (.impI (translation_evaluation _ _ _ _ Prf.hyp0))

theorem translation_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      entry (translated (var 0) (var 1) (var 2)) zero ≐ qone) :=
  closeUniv 3 (.impI (.impI (monic_leading _ _ _ Prf.hyp1 Prf.hyp0)))

theorem translation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 outputF (var 0) (var 1) (var 2) ≐ translated (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

theorem translation_returned_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      ((length (ap3 outputF (var 0) (var 1) (var 2)) ≐ succ (var 1)) ⋏
        (canonicalCoefficients (ap3 outputF (var 0) (var 1) (var 2)) ⋏
          evaluate (ap3 outputF (var 0) (var 1) (var 2)) (var 3) ≐ evaluate (var 0) (qadd (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.andI (returned_length _ _ _)
    (.andI (returned_canonical _ _ _) (returned_evaluation _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalTranslation
