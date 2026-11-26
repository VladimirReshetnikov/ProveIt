import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDilation
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion

/-!
# The actual stored low-degree power prefix

A computed descending buffer reads precisely the original coefficients
through degree d. Its actual evaluator is the original finite power
prefix, and its actual dilation has the original coefficient times t^e.
The original buffer and all three degree indices are numerical.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialLowPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalPolynomialDilation (dilated)
open GaussianRationalPowerExpansion (partialSum)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N d : PTm n) : PTm n := pairT C (pairT N d)
def body : PTm 2 := entry (fstT (var 1)) (monus (fstT (sndT (var 1))) (monus (sndT (sndT (var 1))) (var 0)))
def polynomial (C N d : PTm n) : PTm n := sequence body (succ d) (data C N d)
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C N d : PTm n) :
    Syn.subst σ (data C N d) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (C N d : PTm n) :
    Syn.subst σ (polynomial C N d) = polynomial (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ d) := by simp [polynomial]

theorem body_at (C N d i : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (data C N d) ≐ entry C (monus N (monus d i)) := by
  simp only [body,inst2,Foundations.MasterCertificate.subst_entry,PTm.subst_monus,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (fst_pair _ _) (congrMonus ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrMonus ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)))
theorem polynomial_length (C N d : PTm n) : Γ ⊢[PRAAx] length (polynomial C N d) ≐ succ d := sequence_length _ _ _
theorem polynomial_lookup (C N d i : PTm n) (hi : Γ ⊢[PRAAx] le i d) : Γ ⊢[PRAAx]
    entry (polynomial C N d) i ≐ entry C (monus N (monus d i)) :=
  (sequence_decode body ((succ_monus_succ _ _).eqTrans hi)).eqTrans (body_at C N d i)
theorem original_reader (C N d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    entry (polynomial C N d) (monus d e) ≐ entry C (monus N e) :=
  (polynomial_lookup C N d (monus d e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (entry_congr (.eqRefl _) (congrMonus (.eqRefl _) (GaussianRationalMonicReconstruction.complement d e he)))

theorem original_evaluation (C N d z : PTm n) (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    evaluate (polynomial C N d) z ≐ partialSum C N z (succ d) := by
  refine (GaussianBivariatePowerExpansion.evaluate_power_sum _ _ _ (polynomial_length C N d)).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalPowerExpansion.termBody
      GaussianRationalPowerExpansion.termBody (succ d)
      (GaussianRationalPowerExpansion.data (polynomial C N d) d z)
      (GaussianRationalPowerExpansion.data C N z) (.allI (.impI ?_))).eqTrans ?_)
  · let Δ := lt (var 0) (succ (Syn.shift d)) :: Γ.map Fm.shift
    have h : Δ ⊢[PRAAx] le (var 0) (Syn.shift d) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have eqv := (GaussianRationalPowerExpansion.term_body_at (Γ := Δ)
        (polynomial (Syn.shift C) (Syn.shift N) (Syn.shift d)) (Syn.shift d) (Syn.shift z) (var 0)).eqTrans
      ((qmul_congr (original_reader _ _ _ _ h) (.eqRefl _)).eqTrans
        (GaussianRationalPowerExpansion.term_body_at (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)).eqSymm)
    simpa only [Δ,Syn.shift,subst_polynomial,GaussianRationalPowerExpansion.subst_data,ConciseIPRA.PTm.subst_succ] using eqv
  · exact (GaussianRationalFiniteSum.generated_prefix_congr GaussianRationalPowerExpansion.termBody
      (succ d) (succ N) (GaussianRationalPowerExpansion.data C N z) (succ d) (le_refl _)
        ((succ_monus_succ _ _).eqTrans hd))

theorem dilated_original_reader (C N d t e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    entry (dilated (polynomial C N d) d t) (monus d e) ≐ qmul (entry C (monus N e)) (power t e) :=
  (GaussianRationalPolynomialDilation.dilated_lookup _ _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (qmul_congr (original_reader _ _ _ _ he)
      (congrAp2 powerF (GaussianRationalMonicReconstruction.complement d e he) (.eqRefl _)))

theorem actual_original_low_prefix_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 2) (var 1) ⟶ evaluate (polynomial (var 0) (var 1) (var 2)) (var 3) ≐
      partialSum (var 0) (var 1) (var 3) (succ (var 2))) :=
  closeUniv 4 (.impI (original_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialLowPrefix
