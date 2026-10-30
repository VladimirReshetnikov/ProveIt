import ZFCinPA.SizedDriverBase
import ZFCinPA.SizedStepQuant

/-!
# The bounded driver: quantifier cases

The cases `^∀` and `^∃` of the bounded driver induction.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriver

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le verum_le)
open LeanProofs.ZFCinPA.SizedLNumOK LeanProofs.ZFCinPA.SizedDriverSteps
open LeanProofs.ZFCinPA.SizedEnvForm (Eb Ef0 envForm_le atomOf_le idx_le falsum_le)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LDriver
open LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_val)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

set_option maxHeartbeats 4000000 in
theorem case_all (M : V) :
    ∀ n p, IsSemiformula ℒₛₑₜ (n + 1) p → ΘB (Ad M) Kd (Wd M + 60) M (n + 1) p →
    ΘB (Ad M) Kd (Wd M + 60) M n (^∀ p) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p hp ih hnM
  have hx1 : (^∀ p : V) = ⟪6, p⟫ + 1 := rfl
  have hpx : p ≤ ⟪6, p⟫ := le_pair_right 6 p
  have hnp : n + 1 + p ≤ M := le_trans (by
    rw [hx1, show n + 1 + p = n + (p + 1) by ring]
    exact _root_.add_le_add le_rfl (_root_.add_le_add hpx le_rfl)) hnM
  have hcM : (^∀ p : V) ≤ M := le_trans le_add_self hnM
  have hxM : ⟪6, p⟫ ≤ M := le_trans (show ⟪6, p⟫ ≤ ^∀ p from le_self_add) hcM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih hnp)
  have lP := envF_le hp hnp
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪6, p⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lW : (WbNT (envFormT (n + 1) hp)).val ≤ lvB (Gd M ⟪6, p⟫) :=
    lift_lvB (wbNT_le (two_le_A0 M) lP)
      (le_trans (le_trans le_self_add le_self_add) (Ad_le_Gd M _))
  have lMax : (MaxT F₁ (WbNT (envFormT (n + 1) hp))).val ≤ lvB (Gd M (^∀ p)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lW) (by rw [hx1]; exact Gd_grow M _)
  have hall : (AllT (envFormT (n + 1) hp)).val = envForm n (^∀ p) := by
    rw [allT_val, envForm_all hp.isUFormula]; rfl
  have hsem : IsSemiformula ℒₛₑₜ n (^∀ p) := by simp [hp]
  have lP₀ : (envFormT (n + 1) hp).val ≤ lvB (uD M) := lift_lvB lP (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀ (lift_lvB lF₁ (Gd_le_uD hxM))
    (top_le hu) (lift_lvB lW (Gd_le_uD hxM))
    (hall.trans_le (lift_lvB (envF_le hsem hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := quant_step_le false hu hK (wD_le_W M ⟪6, p⟫) (hF₁.mono (upW M _ _ hpx))
  exact ΘB_of_typed _ hall _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

set_option maxHeartbeats 4000000 in
theorem case_exs (M : V) :
    ∀ n p, IsSemiformula ℒₛₑₜ (n + 1) p → ΘB (Ad M) Kd (Wd M + 60) M (n + 1) p →
    ΘB (Ad M) Kd (Wd M + 60) M n (^∃ p) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p hp ih hnM
  have hx1 : (^∃ p : V) = ⟪7, p⟫ + 1 := rfl
  have hpx : p ≤ ⟪7, p⟫ := le_pair_right 7 p
  have hnp : n + 1 + p ≤ M := le_trans (by
    rw [hx1, show n + 1 + p = n + (p + 1) by ring]
    exact _root_.add_le_add le_rfl (_root_.add_le_add hpx le_rfl)) hnM
  have hcM : (^∃ p : V) ≤ M := le_trans le_add_self hnM
  have hxM : ⟪7, p⟫ ≤ M := le_trans (show ⟪7, p⟫ ≤ ^∃ p from le_self_add) hcM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih hnp)
  have lP := envF_le hp hnp
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪7, p⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lW : (WbT (envFormT (n + 1) hp)).val ≤ lvB (Gd M ⟪7, p⟫) :=
    lift_lvB (wbT_le (two_le_A0 M) lP)
      (le_trans (le_trans le_self_add le_self_add) (Ad_le_Gd M _))
  have lMax : (MaxT F₁ (WbT (envFormT (n + 1) hp))).val ≤ lvB (Gd M (^∃ p)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lW) (by rw [hx1]; exact Gd_grow M _)
  have hex : (ExT (envFormT (n + 1) hp)).val = envForm n (^∃ p) := by
    rw [exT_val, envForm_exs hp.isUFormula]; rfl
  have hsem : IsSemiformula ℒₛₑₜ n (^∃ p) := by simp [hp]
  have lP₀ : (envFormT (n + 1) hp).val ≤ lvB (uD M) := lift_lvB lP (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀ (lift_lvB lF₁ (Gd_le_uD hxM))
    (top_le hu) (lift_lvB lW (Gd_le_uD hxM))
    (hex.trans_le (lift_lvB (envF_le hsem hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := quant_step_le true hu hK (wD_le_W M ⟪7, p⟫) (hF₁.mono (upW M _ _ hpx))
  exact ΘB_of_typed _ hex _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

end LeanProofs.ZFCinPA.SizedDriver
