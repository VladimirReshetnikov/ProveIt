import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues

/-!
# Actual triangular coefficient identities for translation stages

Ascending coefficients of the actual successive synthetic quotients are
canonically recoded. Their constant, interior and leading identities are
derived from the actual quotient recurrence, retaining arbitrary raw
original coefficients. The terminal singleton and original stage are
linked explicitly. No inverse-translation formula is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr recode_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient qsub_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (stage remaining remaining_step)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (C N z j k : PTm n) : PTm n := recode (entry (stage C N z j) (monus (remaining N j) k))
def translatedCoefficient (C N z j : PTm n) : PTm n := evaluate (stage C N z j) z
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (C N z j k : PTm n) :
    Syn.subst σ (coefficient C N z j k) = coefficient (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ j) (Syn.subst σ k) := by simp [coefficient]
@[simp] theorem subst_translatedCoefficient {m : ℕ} (σ : Fin n → PTm m) (C N z j : PTm n) :
    Syn.subst σ (translatedCoefficient C N z j) = translatedCoefficient (Syn.subst σ C)
      (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ j) := by simp [translatedCoefficient]

theorem coefficient_canonical (C N z j k : PTm n) : Γ ⊢[PRAAx] canonical (coefficient C N z j k) :=
  recode_canonical _
theorem translated_coefficient_canonical (C N z j : PTm n) : Γ ⊢[PRAAx]
    canonical (translatedCoefficient C N z j) := GaussianRationalHorner.horner_canonical _ _ _

theorem coefficient_index_congr (C N z j : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx]
    coefficient C N z j k ≐ coefficient C N z j l :=
  recode_congr (entry_congr (.eqRefl _) (congrMonus (.eqRefl _) h))

theorem translated_zero (C N z : PTm n) : Γ ⊢[PRAAx]
    translatedCoefficient C N z zero ≐ evaluate C z :=
  GaussianRationalTranslation.evaluate_congr (GaussianRationalTranslationStages.stage_zero C N z) (.eqRefl _)

theorem original_coefficient (C N z k : PTm n) : Γ ⊢[PRAAx]
    coefficient C N z zero k ≐ recode (entry C (monus N k)) :=
  recode_congr (entry_congr (GaussianRationalTranslationStages.stage_zero C N z)
    (congrMonus (monus_zero N) (.eqRefl _)))

theorem translated_coefficient_at (C N z j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    translatedCoefficient C N z j ≐ GaussianBalancedRadiusSyntax.coefficient
      (GaussianRationalTranslation.translated C N z) N j :=
  (GaussianRationalTranslation.ascending_coefficient C N z j hj).eqSymm

theorem next_coefficient_index (C N z j k i : PTm n)
    (hi : Γ ⊢[PRAAx] monus (remaining N (succ j)) k ≐ i) : Γ ⊢[PRAAx]
    coefficient C N z (succ j) k ≐ recode (entry (quotient (stage C N z j) z (remaining N j)) i) :=
  recode_congr (entry_congr (GaussianRationalTranslationStages.stage_succ C N z j) hi)

theorem remaining_pred (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    remaining N (succ j) ≐ pred (remaining N j) :=
  ((congrPred (remaining_step N j hj)).eqTrans (pred_succ _)).eqSymm

/-- The actual constant coefficient is recovered from the actual
stage evaluation and the actual next quotient's constant coefficient. -/
theorem constant_coefficient (C N z j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    coefficient C N z j zero ≐ qsub (translatedCoefficient C N z j)
      (qmul z (coefficient C N z (succ j) zero)) := by
  have len := GaussianRationalTranslationStages.stage_length C N z j hLen (le_of_lt hj)
  have actual := GaussianRationalSyntheticCoefficientValues.constant_coefficient
    (stage C N z j) z (remaining N j) len (GaussianRationalTranslationStages.remaining_positive N j hj)
  have next := next_coefficient_index C N z j zero (pred (remaining N j))
    ((monus_zero _).eqTrans (remaining_pred N j hj))
  exact (recode_congr (entry_congr (.eqRefl _) (monus_zero _))).eqTrans
    (actual.eqTrans (qsub_congr (.eqRefl _) (qmul_congr (.eqRefl _) next.eqSymm)))

/-- The two index identities are proved from internal inequalities;
no predecessor or truncated-subtraction equality is assumed. -/
theorem interior_indices (M k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkM : Γ ⊢[PRAAx] lt k M) : Γ ⊢[PRAAx]
    (le one (monus M k) ⋏ (lt (monus M k) M ⋏
      (monus (pred M) (pred k) ≐ monus M k ⋏ monus (pred M) k ≐ pred (monus M k)))) := by
  have pos := GaussianRationalTranslationStages.remaining_positive M k hkM
  have Mpos : Γ ⊢[PRAAx] le one M := le_trans hk (le_of_lt hkM)
  have first : Γ ⊢[PRAAx] monus (pred M) (pred k) ≐ monus M k :=
    ((congrMonus (RationalIntegerNormalization.positive_form Mpos)
      (RationalIntegerNormalization.positive_form hk)).eqTrans (succ_monus_succ _ _)).eqSymm
  have shape : Γ ⊢[PRAAx] M ≐ succ (k+monus M (succ k)) :=
    (eq_add_of_le hkM).eqTrans (by ipra_ring)
  have left : Γ ⊢[PRAAx] monus (pred M) k ≐ monus M (succ k) :=
    (congrMonus ((congrPred shape).eqTrans (pred_succ _)) (.eqRefl _)).eqTrans (add_monus' _ _)
  have right : Γ ⊢[PRAAx] pred (monus M k) ≐ monus M (succ k) :=
    (congrPred (remaining_step M k hkM)).eqTrans (pred_succ _)
  have short : Γ ⊢[PRAAx] lt (monus M k) M := le_of_eq_add (d := pred k)
    (((eq_add_of_le (le_of_lt hkM)).eqTrans
      (congrAdd (RationalIntegerNormalization.positive_form hk) (.eqRefl _))).eqTrans (by ipra_ring))
  exact .andI pos (.andI short (.andI first (left.eqTrans right.eqSymm)))

/-- The actual interior ascending coefficient is a difference of two
adjacent actual next-stage ascending coefficients. -/
theorem interior_coefficient (C N z j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] le one k) (hkM : Γ ⊢[PRAAx] lt k (remaining N j)) : Γ ⊢[PRAAx]
    coefficient C N z j k ≐ qsub (coefficient C N z (succ j) (pred k))
      (qmul z (coefficient C N z (succ j) k)) := by
  have indices := interior_indices (remaining N j) k hk hkM
  have actual := GaussianRationalSyntheticCoefficientValues.interior_coefficient
    (stage C N z j) z (remaining N j) (monus (remaining N j) k)
    (Prf.andE₁ indices) (Prf.andE₁ (Prf.andE₂ indices))
  have indexLeft : Γ ⊢[PRAAx] monus (remaining N (succ j)) (pred k) ≐ monus (remaining N j) k :=
    (congrMonus (remaining_pred N j hj) (.eqRefl _)).eqTrans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ indices)))
  have indexRight : Γ ⊢[PRAAx] monus (remaining N (succ j)) k ≐ pred (monus (remaining N j) k) :=
    (congrMonus (remaining_pred N j hj) (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ indices)))
  exact actual.eqTrans (qsub_congr (next_coefficient_index C N z j (pred k) _ indexLeft).eqSymm
    (qmul_congr (.eqRefl _) (next_coefficient_index C N z j k _ indexRight).eqSymm))

/-- The leading case is separate; no out-of-range totalized entry is
silently interpreted as a canonical zero. -/
theorem leading_coefficient (C N z j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    coefficient C N z j (remaining N j) ≐ coefficient C N z (succ j) (pred (remaining N j)) := by
  have actual := GaussianRationalSyntheticCoefficientValues.leading_coefficient
    (stage C N z j) z (remaining N j) (GaussianRationalTranslationStages.remaining_positive N j hj)
  have index : Γ ⊢[PRAAx] monus (remaining N (succ j)) (pred (remaining N j)) ≐ zero :=
    (congrMonus (remaining_pred N j hj) (.eqRefl _)).eqTrans (monus_self _)
  exact (recode_congr (entry_congr (.eqRefl _) (monus_self _))).eqTrans
    (actual.eqTrans (next_coefficient_index C N z j _ zero index).eqSymm)

theorem leading_coefficient_at (C N z j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] k ≐ remaining N j) : Γ ⊢[PRAAx]
    coefficient C N z j k ≐ coefficient C N z (succ j) (pred k) :=
  (coefficient_index_congr C N z j hk).eqTrans ((leading_coefficient C N z j hj).eqTrans
    (coefficient_index_congr C N z (succ j) (congrPred hk.eqSymm)))

theorem terminal_coefficient (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    coefficient C N z N zero ≐ translatedCoefficient C N z N := by
  have index : Γ ⊢[PRAAx] monus (remaining N N) zero ≐ zero :=
    (monus_zero _).eqTrans (monus_self _)
  exact (recode_congr (entry_congr (.eqRefl _) index)).eqTrans
    (GaussianRationalSyntheticCoefficientValues.singleton_evaluation _ z
      (GaussianRationalTranslationStages.terminal_length C N z hLen))

/-! The two evaluators are fixed PR programs with all numerical degrees,
stage indices and coefficient positions as ordinary runtime arguments. -/
def coefficientF : PR 5 := PTm.toPR (coefficient (var 0) (var 1) (var 2) (var 3) (var 4))
def translatedCoefficientF : PR 4 := PTm.toPR (translatedCoefficient (var 0) (var 1) (var 2) (var 3))
def run (C N z j k : PTm n) : PTm n := PTm.app coefficientF ![C,N,z,j,k]
def translatedRun (C N z j : PTm n) : PTm n := PTm.app translatedCoefficientF ![C,N,z,j]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z j k : PTm n) :
    Syn.subst σ (run C N z j k) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_translatedRun {m : ℕ} (σ : Fin n → PTm m) (C N z j : PTm n) :
    Syn.subst σ (translatedRun C N z j) = translatedRun (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ j) := by
  simp only [translatedRun,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N z j k : PTm n) : Γ ⊢[PRAAx] run C N z j k ≐ coefficient C N z j k := by
  simpa [run,coefficientF] using toPR_eq (Γ := Γ)
    (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,z,j,k]
theorem translated_program_at (C N z j : PTm n) : Γ ⊢[PRAAx]
    translatedRun C N z j ≐ translatedCoefficient C N z j := by
  simpa [translatedRun,translatedCoefficientF] using toPR_eq (Γ := Γ)
    (translatedCoefficient (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,z,j]

theorem returned_constant_identity (C N z j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    run C N z j zero ≐ qsub (translatedRun C N z j) (qmul z (run C N z (succ j) zero)) :=
  (program_at C N z j zero).eqTrans ((constant_coefficient C N z j hLen hj).eqTrans
    (qsub_congr (translated_program_at C N z j).eqSymm
      (qmul_congr (.eqRefl _) (program_at C N z (succ j) zero).eqSymm)))

theorem constant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ lt (var 3) (var 1) ⟶ coefficient (var 0) (var 1) (var 2) (var 3) zero ≐
      qsub (translatedCoefficient (var 0) (var 1) (var 2) (var 3))
        (qmul (var 2) (coefficient (var 0) (var 1) (var 2) (succ (var 3)) zero))) :=
  closeUniv 4 (.impI (.impI (constant_coefficient _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem interior_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ le one (var 4) ⟶ lt (var 4) (remaining (var 1) (var 3)) ⟶
      coefficient (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        qsub (coefficient (var 0) (var 1) (var 2) (succ (var 3)) (pred (var 4)))
          (qmul (var 2) (coefficient (var 0) (var 1) (var 2) (succ (var 3)) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (interior_coefficient _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem leading_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ coefficient (var 0) (var 1) (var 2) (var 3) (remaining (var 1) (var 3)) ≐
      coefficient (var 0) (var 1) (var 2) (succ (var 3)) (pred (remaining (var 1) (var 3)))) :=
  closeUniv 4 (.impI (leading_coefficient _ _ _ _ Prf.hyp0))
theorem terminal_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ coefficient (var 0) (var 1) (var 2) (var 1) zero ≐
      translatedCoefficient (var 0) (var 1) (var 2) (var 1)) :=
  closeUniv 3 (.impI (terminal_coefficient _ _ _ Prf.hyp0))
theorem original_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coefficient (var 0) (var 1) (var 2) zero (var 3) ≐ recode (entry (var 0) (monus (var 1) (var 3)))) :=
  closeUniv 4 (original_coefficient _ _ _ _)
theorem actual_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ coefficient (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (translatedRun (var 0) (var 1) (var 2) (var 3) ≐ translatedCoefficient (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (translated_program_at _ _ _ _))
theorem returned_constant_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ lt (var 3) (var 1) ⟶ run (var 0) (var 1) (var 2) (var 3) zero ≐
      qsub (translatedRun (var 0) (var 1) (var 2) (var 3))
        (qmul (var 2) (run (var 0) (var 1) (var 2) (succ (var 3)) zero))) :=
  closeUniv 4 (.impI (.impI (returned_constant_identity _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientValues
