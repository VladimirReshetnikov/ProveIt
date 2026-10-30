import ZFCinPA.SizedDriverBase
import ZFCinPA.SizedStepConn

/-!
# The bounded driver: connective cases

The cases `^⋏` and `^⋎` of the bounded driver induction.
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
theorem case_and (M : V) :
    ∀ n p q, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
    ΘB (Ad M) Kd (Wd M + 60) M n p → ΘB (Ad M) Kd (Wd M + 60) M n q →
    ΘB (Ad M) Kd (Wd M + 60) M n (p ^⋏ q) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p q hp hq ih₁ ih₂ hnM
  have hx1 : (p ^⋏ q : V) = ⟪4, p, q⟫ + 1 := rfl
  have hpx : p ≤ ⟪4, p, q⟫ := le_trans (le_pair_left p q) (le_pair_right 4 _)
  have hqx : q ≤ ⟪4, p, q⟫ := le_trans (le_pair_right p q) (le_pair_right 4 _)
  have hnp : n + p ≤ M := le_trans (_root_.add_le_add le_rfl (lt_K!_left p q).le) hnM
  have hnq : n + q ≤ M := le_trans (_root_.add_le_add le_rfl (lt_K!_right p q).le) hnM
  have hcM : p ^⋏ q ≤ M := le_trans le_add_self hnM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih₁ hnp)
  obtain ⟨F₃, hF₃l, hF₃⟩ := typed_of_ΘB hq (ih₂ hnq)
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪4, p, q⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lF₃ : F₃.val ≤ lvB (Gd M ⟪4, p, q⟫) := lift_lvB hF₃l (Gd_mono M hqx)
  have lMax : (MaxT F₁ F₃).val ≤ lvB (Gd M (p ^⋏ q)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lF₃) (by rw [hx1]; exact Gd_grow M _)
  have hpq : (envFormT n hp ⋏ envFormT n hq).val = envForm n (p ^⋏ q) := by
    simp [envFormT, envForm_and hp.isUFormula hq.isUFormula]
  have hsem : IsSemiformula ℒₛₑₜ n (p ^⋏ q) := by simp [hp, hq]
  have hxM : ⟪4, p, q⟫ ≤ M := le_trans (show ⟪4, p, q⟫ ≤ p ^⋏ q from le_self_add) hcM
  have lP₀ : (envFormT n hp).val ≤ lvB (uD M) := lift_lvB (envF_le hp hnp) (A0_le_uD M)
  have lP₂ : (envFormT n hq).val ≤ lvB (uD M) := lift_lvB (envF_le hq hnq) (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀
    (lift_lvB lF₁ (Gd_le_uD hxM)) lP₂
    (lift_lvB lF₃ (Gd_le_uD hxM))
    (hpq.trans_le (lift_lvB (envF_le hsem hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := and_step_le hu hK (wD_le_W M ⟪4, p, q⟫) (hF₁.mono (upW M _ _ hpx))
    (hF₃.mono (upW M _ _ hqx))
  exact ΘB_of_typed _ hpq _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

set_option maxHeartbeats 4000000 in
theorem case_or (M : V) :
    ∀ n p q, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
    ΘB (Ad M) Kd (Wd M + 60) M n p → ΘB (Ad M) Kd (Wd M + 60) M n q →
    ΘB (Ad M) Kd (Wd M + 60) M n (p ^⋎ q) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p q hp hq ih₁ ih₂ hnM
  have hx1 : (p ^⋎ q : V) = ⟪5, p, q⟫ + 1 := rfl
  have hpx : p ≤ ⟪5, p, q⟫ := le_trans (le_pair_left p q) (le_pair_right 5 _)
  have hqx : q ≤ ⟪5, p, q⟫ := le_trans (le_pair_right p q) (le_pair_right 5 _)
  have hnp : n + p ≤ M := le_trans (_root_.add_le_add le_rfl (lt_or_left p q).le) hnM
  have hnq : n + q ≤ M := le_trans (_root_.add_le_add le_rfl (lt_or_right p q).le) hnM
  have hcM : p ^⋎ q ≤ M := le_trans le_add_self hnM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih₁ hnp)
  obtain ⟨F₃, hF₃l, hF₃⟩ := typed_of_ΘB hq (ih₂ hnq)
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪5, p, q⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lF₃ : F₃.val ≤ lvB (Gd M ⟪5, p, q⟫) := lift_lvB hF₃l (Gd_mono M hqx)
  have lMax : (MaxT F₁ F₃).val ≤ lvB (Gd M (p ^⋎ q)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lF₃) (by rw [hx1]; exact Gd_grow M _)
  have hpq : (envFormT n hp ⋎ envFormT n hq).val = envForm n (p ^⋎ q) := by
    simp [envFormT, envForm_or hp.isUFormula hq.isUFormula]
  have hsem : IsSemiformula ℒₛₑₜ n (p ^⋎ q) := by simp [hp, hq]
  have hxM : ⟪5, p, q⟫ ≤ M := le_trans (show ⟪5, p, q⟫ ≤ p ^⋎ q from le_self_add) hcM
  have lP₀ : (envFormT n hp).val ≤ lvB (uD M) := lift_lvB (envF_le hp hnp) (A0_le_uD M)
  have lP₂ : (envFormT n hq).val ≤ lvB (uD M) := lift_lvB (envF_le hq hnq) (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀
    (lift_lvB lF₁ (Gd_le_uD hxM)) lP₂
    (lift_lvB lF₃ (Gd_le_uD hxM))
    (hpq.trans_le (lift_lvB (envF_le hsem hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := or_step_le hu hK (wD_le_W M ⟪5, p, q⟫) (hF₁.mono (upW M _ _ hpx))
    (hF₃.mono (upW M _ _ hqx))
  exact ΘB_of_typed _ hpq _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

end LeanProofs.ZFCinPA.SizedDriver
