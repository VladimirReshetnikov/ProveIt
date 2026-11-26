import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationCoefficientValues
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalTravelScaling
import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationCoefficientMaximum

/-!
# Actual radius-scaled translation coefficient recurrences

Each actual stage coefficient is multiplied by the exact rational radius
power indexed by its stage plus its ascending degree. Actual synthetic
coefficient identities and the actual reciprocal radius derive the local
triangular recurrences in these common units. All numerical degrees,
stages, radii and coefficient codes are internal; no recurrence, scaling
identity, bound or maximum condition is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslationScaledCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (powerF)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (remaining)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaledCoefficient (C N z A B j k : PTm n) : PTm n :=
  GaussianRationalTravelScaling.scaled A B (j+k) (GaussianTranslationCoefficientValues.coefficient C N z j k)
@[simp] theorem subst_scaledCoefficient {m : ℕ} (σ : Fin n → PTm m) (C N z A B j k : PTm n) :
    Syn.subst σ (scaledCoefficient C N z A B j k) = scaledCoefficient (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by simp [scaledCoefficient]

theorem scaled_congr (A B : PTm n) {e f c d : PTm n} (he : Γ ⊢[PRAAx] e ≐ f)
    (hc : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx]
    GaussianRationalTravelScaling.scaled A B e c ≐ GaussianRationalTravelScaling.scaled A B f d :=
  qmul_congr (congrAp2 powerF he (.eqRefl _)) hc

theorem scaledCoefficient_canonical (C N z A B j k : PTm n) : Γ ⊢[PRAAx]
    canonical (scaledCoefficient C N z A B j k) := GaussianRationalHorner.qmul_canonical _ _

theorem scaledCoefficient_index_congr (C N z A B j : PTm n) {k l : PTm n}
    (h : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx] scaledCoefficient C N z A B j k ≐ scaledCoefficient C N z A B j l :=
  scaled_congr A B (congrAdd (.eqRefl _) h) (GaussianTranslationCoefficientValues.coefficient_index_congr C N z j h)

theorem scaledCoefficient_stage_congr (C N z A B k : PTm n) {j l : PTm n}
    (h : Γ ⊢[PRAAx] j ≐ l) : Γ ⊢[PRAAx] scaledCoefficient C N z A B j k ≐ scaledCoefficient C N z A B l k :=
  scaled_congr A B (congrAdd h (.eqRefl _))
    (GaussianTranslatedNonconstant.recode_congr (Foundations.SequenceComposition.entry_congr
      (GaussianRationalTranslationStages.stage_index_congr C N z h)
      (congrMonus (congrMonus (.eqRefl _) h) (.eqRefl _))))

/-- The actual constant row has an actual weighted translated term, so
its nonconstant-stage budget can later use the computed maximum. -/
theorem constant_coefficient (C N z A B j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B j zero ≐ qsub (GaussianTranslationCoefficientMaximum.term C N z A B j)
      (qmul (GaussianRationalTravelScaling.ratio A B z) (scaledCoefficient C N z A B (succ j) zero)) := by
  have actual := scaled_congr A B (add_zero j) (GaussianTranslationCoefficientValues.constant_coefficient C N z j hLen hj)
  exact actual.eqTrans ((GaussianRationalTravelScaling.scaled_difference A B z j _ _ hA hB).eqTrans
    (qsub_congr (.eqRefl _) (qmul_congr (.eqRefl _) (scaled_congr A B (add_zero (succ j)).eqSymm (.eqRefl _)))))

/-- Positive k aligns the two original exponent formulas exactly; no
numerical magnitude or U>=1 assumption enters this arithmetic identity. -/
theorem interior_coefficient (C N z A B j k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hj : Γ ⊢[PRAAx] lt j N) (hk : Γ ⊢[PRAAx] le one k)
    (hkM : Γ ⊢[PRAAx] lt k (remaining N j)) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B j k ≐ qsub (scaledCoefficient C N z A B (succ j) (pred k))
      (qmul (GaussianRationalTravelScaling.ratio A B z) (scaledCoefficient C N z A B (succ j) k)) := by
  have actual := scaled_congr A B (.eqRefl (j+k)) (GaussianTranslationCoefficientValues.interior_coefficient C N z j k hj hk hkM)
  have leftIndex : Γ ⊢[PRAAx] j+k ≐ succ j+pred k :=
    (congrAdd (.eqRefl _) (RationalIntegerNormalization.positive_form hk)).eqTrans (by ipra_ring)
  have rightIndex : Γ ⊢[PRAAx] succ (j+k) ≐ succ j+k := by ipra_ring
  exact actual.eqTrans ((GaussianRationalTravelScaling.scaled_difference A B z (j+k) _ _ hA hB).eqTrans
    (qsub_congr (scaled_congr A B leftIndex (.eqRefl _))
      (qmul_congr (.eqRefl _) (scaled_congr A B rightIndex (.eqRefl _)))))

theorem leading_coefficient (C N z A B j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B j (remaining N j) ≐
      scaledCoefficient C N z A B (succ j) (pred (remaining N j)) := by
  have exponent : Γ ⊢[PRAAx] j+remaining N j ≐ succ j+pred (remaining N j) :=
    (congrAdd (.eqRefl _) (RationalIntegerNormalization.positive_form
      (GaussianRationalTranslationStages.remaining_positive N j hj))).eqTrans (by ipra_ring)
  exact scaled_congr A B exponent (GaussianTranslationCoefficientValues.leading_coefficient C N z j hj)

theorem leading_coefficient_at (C N z A B j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] k ≐ remaining N j) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B j k ≐ scaledCoefficient C N z A B (succ j) (pred k) :=
  (scaledCoefficient_index_congr C N z A B j hk).eqTrans ((leading_coefficient C N z A B j hj).eqTrans
    (scaledCoefficient_index_congr C N z A B (succ j) (congrPred hk.eqSymm)))

theorem terminal_coefficient (C N z A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B N zero ≐ GaussianTranslationCoefficientMaximum.term C N z A B N :=
  scaled_congr A B (add_zero N) (GaussianTranslationCoefficientValues.terminal_coefficient C N z hLen)

theorem original_coefficient (C N z A B k : PTm n) : Γ ⊢[PRAAx]
    scaledCoefficient C N z A B zero k ≐ GaussianRationalTravelScaling.scaled A B k
      (GaussianTranslatedNonconstant.recode (entry C (monus N k))) :=
  scaled_congr A B (zero_add k) (GaussianTranslationCoefficientValues.original_coefficient C N z k)

def scaledCoefficientF : PR 7 := PTm.toPR
  (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (C N z A B j k : PTm n) : PTm n := PTm.app scaledCoefficientF ![C,N,z,A,B,j,k]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z A B j k : PTm n) :
    Syn.subst σ (run C N z A B j k) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N z A B j k : PTm n) : Γ ⊢[PRAAx]
    run C N z A B j k ≐ scaledCoefficient C N z A B j k := by
  simpa [run,scaledCoefficientF] using toPR_eq (Γ := Γ)
    (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![C,N,z,A,B,j,k]

theorem returned_constant_identity (C N z A B j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    run C N z A B j zero ≐ qsub (GaussianTranslationCoefficientMaximum.term C N z A B j)
      (qmul (GaussianRationalTravelScaling.ratio A B z) (run C N z A B (succ j) zero)) :=
  (program_at C N z A B j zero).eqTrans ((constant_coefficient C N z A B j hLen hA hB hj).eqTrans
    (qsub_congr (.eqRefl _) (qmul_congr (.eqRefl _) (program_at C N z A B (succ j) zero).eqSymm)))

theorem constant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 1) ⟶ le one (var 3) ⟶ le one (var 4) ⟶ lt (var 5) (var 1) ⟶
      scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) zero ≐
        qsub (GaussianTranslationCoefficientMaximum.term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (qmul (GaussianRationalTravelScaling.ratio (var 3) (var 4) (var 2))
            (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) zero))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (constant_coefficient _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem interior_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 3) ⟶ le one (var 4) ⟶ lt (var 5) (var 1) ⟶ le one (var 6) ⟶
      lt (var 6) (remaining (var 1) (var 5)) ⟶
      scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
        qsub (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (pred (var 6)))
          (qmul (GaussianRationalTravelScaling.ratio (var 3) (var 4) (var 2))
            (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (var 6)))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (interior_coefficient _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem leading_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 1) ⟶
      scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (remaining (var 1) (var 5)) ≐
        scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (pred (remaining (var 1) (var 5)))) :=
  closeUniv 6 (.impI (leading_coefficient _ _ _ _ _ _ Prf.hyp0))
theorem terminal_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶
      scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 1) zero ≐
        GaussianTranslationCoefficientMaximum.term (var 0) (var 1) (var 2) (var 3) (var 4) (var 1)) :=
  closeUniv 5 (.impI (terminal_coefficient _ _ _ _ _ Prf.hyp0))
theorem original_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) zero (var 5) ≐
      GaussianRationalTravelScaling.scaled (var 3) (var 4) (var 5)
        (GaussianTranslatedNonconstant.recode (entry (var 0) (monus (var 1) (var 5))))) :=
  closeUniv 6 (original_coefficient _ _ _ _ _ _)
theorem actual_scaled_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      scaledCoefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem returned_constant_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 1) ⟶ le one (var 3) ⟶ le one (var 4) ⟶ lt (var 5) (var 1) ⟶
      run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) zero ≐
        qsub (GaussianTranslationCoefficientMaximum.term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (qmul (GaussianRationalTravelScaling.ratio (var 3) (var 4) (var 2))
            (run (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) zero))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_constant_identity _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianTranslationScaledCoefficients
