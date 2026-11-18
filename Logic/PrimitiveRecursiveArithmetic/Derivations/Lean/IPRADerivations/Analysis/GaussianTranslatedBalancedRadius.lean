import IPRADerivations.Analysis.GaussianRationalTranslation
import IPRADerivations.Analysis.GaussianMonicNonconstant

/-!
# Actual translation and balanced radius for the original monic input

The only polynomial input is the original descending list C and its degree.
The computed translated list has constant coefficient exactly P(z), and
its evaluator is exactly P(z+W). Monicity supplies the nonconstant witness
for the actual balanced-radius program. Both residual branches therefore
refer to the original evaluated residual, with no supplied translation,
height or successful-search certificate. All numerical data are internal.

Dominant plateau, direction and full contraction are still separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslatedBalancedRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputContract (C N : PTm n) : Fm PTm n := length C ≐ succ N ⋏ (le one N ⋏ entry C zero ≐ qone)
def residual (C z : PTm n) : PTm n := normSq (rawGaussian (evaluate C z))
def radius (C N z : PTm n) : PTm n := GaussianBalancedRadius.radius (translated C N z) N

@[simp] theorem subst_inputContract {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (inputContract C N).subst σ = inputContract (Syn.subst σ C) (Syn.subst σ N) := by simp [inputContract]
@[simp] theorem subst_residual {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (residual C z) = residual (Syn.subst σ C) (Syn.subst σ z) := by simp [residual]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (radius C N z) = radius (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [radius]

theorem constant_coefficient (C N z : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (translated C N z) N zero ≐ evaluate C z :=
  (Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_zero N)).eqTrans
    (GaussianRationalTranslation.constant_coefficient C N z)

theorem residual_identity (C N z : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.numerator (translated C N z) N zero ≐ residual C z :=
  GaussianMonicNonconstant.raw_norm_congr (constant_coefficient C N z)

theorem radius_input (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    GaussianBalancedRadius.inputContract (translated C N z) N :=
  GaussianMonicNonconstant.radius_input _ N (GaussianRationalTranslation.translated_length C N z)
    (Prf.andE₁ (Prf.andE₂ h)) (GaussianRationalTranslation.monic_leading C N z (Prf.andE₁ h) (Prf.andE₂ (Prf.andE₂ h)))

/-- The zero branch is controlled by the original actual residual P(z). -/
theorem zero_radius (C N z : PTm n) (h0 : Γ ⊢[PRAAx] residual C z ≐ zero) : Γ ⊢[PRAAx]
    radius C N z ≐ fraction zero one :=
  GaussianBalancedRadius.radius_zero _ _ ((residual_identity C N z).eqTrans h0)

/-- The positive branch supplies the original residual to the actual
scan producer, including its same computed coefficient witness. -/
theorem positive_branch (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (h0 : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    GaussianBalancedRadius.balancedBranch (translated C N z) N :=
  GaussianBalancedRadius.positive_balanced_branch _ _ (radius_input C N z h)
    (le_congr (.eqRefl _) (residual_identity C N z).eqSymm h0)

def translationLaw (C N z : PTm n) : Fm PTm n := .all
  (evaluate (translated (Syn.shift C) (Syn.shift N) (Syn.shift z)) (var 0) ≐
    evaluate (Syn.shift C) (qadd (Syn.shift z) (var 0)))

@[simp] theorem subst_translationLaw {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    (translationLaw C N z).subst σ = translationLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by
  simp [translationLaw,Syn.subst_shift,Syn.shift_subst]

theorem translation_law (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    translationLaw C N z := by
  refine .allI ?_
  have shape : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
      ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  exact GaussianRationalTranslation.translation_evaluation _ _ _ (var 0) shape

def certificate (C N z : PTm n) : Fm PTm n :=
  GaussianRationalSyntheticDivision.canonicalCoefficients (translated C N z) ⋏
  (length (translated C N z) ≐ succ N ⋏
  (entry (translated C N z) zero ≐ qone ⋏
  (GaussianBalancedRadiusSyntax.coefficient (translated C N z) N zero ≐ evaluate C z ⋏
  (translationLaw C N z ⋏
  (GaussianBalancedRadius.certificate (translated C N z) N ⋏
  ((residual C z ≐ zero ⟶ radius C N z ≐ fraction zero one) ⋏
   (le one (residual C z) ⟶ GaussianBalancedRadius.balancedBranch (translated C N z) N)))))))

@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    (certificate C N z).subst σ = certificate (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [certificate]

theorem translated_balanced_radius (C N z : PTm n) (h : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    certificate C N z :=
  .andI (GaussianRationalTranslation.translated_canonical C N z)
    (.andI (GaussianRationalTranslation.translated_length C N z)
      (.andI (GaussianRationalTranslation.monic_leading C N z (Prf.andE₁ h) (Prf.andE₂ (Prf.andE₂ h)))
        (.andI (constant_coefficient C N z) (.andI (translation_law C N z (Prf.andE₁ h))
          (.andI (GaussianBalancedRadius.balanced_radius _ _ (radius_input C N z h))
            (.andI (.impI (zero_radius C N z Prf.hyp0)) (.impI (positive_branch C N z h.wk Prf.hyp0))))))))

def output (C N z : PTm n) : PTm n :=
  pairT (translated C N z) (ap2 GaussianBalancedRadius.outputF (translated C N z) N)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N z : PTm n) : PTm n := ap3 outputF C N z

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (output C N z) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (run C N z) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [run]

theorem program_at (C N z : PTm n) : Γ ⊢[PRAAx] run C N z ≐ output C N z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,z]

theorem returned_polynomial (C N z : PTm n) : Γ ⊢[PRAAx] fstT (run C N z) ≐ translated C N z :=
  (congrFst (program_at C N z)).eqTrans (fst_pair _ _)

theorem returned_radius (C N z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N z)) ≐ radius C N z :=
  (congrFst ((congrSnd (program_at C N z)).eqTrans (snd_pair _ _))).eqTrans (GaussianBalancedRadius.returned_radius _ _)

theorem returned_constant (C N z : PTm n) : Γ ⊢[PRAAx]
    entry (fstT (run C N z)) N ≐ evaluate C z :=
  (Foundations.SequenceComposition.entry_congr (returned_polynomial C N z) (.eqRefl _)).eqTrans
    (GaussianRationalTranslation.constant_coefficient C N z)

theorem translated_balanced_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ certificate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (translated_balanced_radius _ _ _ Prf.hyp0))

theorem translated_balanced_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      ((fstT (run (var 0) (var 1) (var 2)) ≐ translated (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ radius (var 0) (var 1) (var 2)) ⋏
          entry (fstT (run (var 0) (var 1) (var 2))) (var 1) ≐ evaluate (var 0) (var 2)))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_polynomial _ _ _) (.andI (returned_radius _ _ _) (returned_constant _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianTranslatedBalancedRadius
