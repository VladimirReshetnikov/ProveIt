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
/-- **The binary-connective case**, for a connective `op` coded as `⟪t, p, q⟫ + 1`
whose bounded invariant step is `step`. -/
theorem case_bin (M : V) {cop : V → V → V} {t : V} (hx1 : ∀ p q, cop p q = ⟪t, p, q⟫ + 1)
    (op : SF V 1 → SF V 1 → SF V 1)
    (step : ∀ {P₀ P₂ : SF V 1} {F₁ F₃ : SF V 2} {u w : V}, 2 ≤ u →
      (∀ i, (K6 P₀ F₁ P₂ F₃ (op P₀ P₂) (MaxT F₁ F₃) i).val ≤ lvB u) → wD u ≤ w →
      DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w → DLv 𝗭𝗙 (insert (InvT P₂ F₃).val ∅) w →
      DLv 𝗭𝗙 (insert (InvT (op P₀ P₂) (MaxT F₁ F₃)).val ∅) (w + 30))
    (ltl : ∀ p q, p < cop p q) (ltr : ∀ p q, q < cop p q)
    (hsem : ∀ {n p q : V}, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
      IsSemiformula ℒₛₑₜ n (cop p q))
    (henv : ∀ {n p q : V} (hp : IsSemiformula ℒₛₑₜ n p) (hq : IsSemiformula ℒₛₑₜ n q),
      (op (envFormT n hp) (envFormT n hq)).val = envForm n (cop p q)) :
    ∀ n p q, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
    ΘB (Ad M) Kd (Wd M + 60) M n p → ΘB (Ad M) Kd (Wd M + 60) M n q →
    ΘB (Ad M) Kd (Wd M + 60) M n (cop p q) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p q hp hq ih₁ ih₂ hnM
  have hpx : p ≤ ⟪t, p, q⟫ := le_trans (le_pair_left p q) (le_pair_right t _)
  have hqx : q ≤ ⟪t, p, q⟫ := le_trans (le_pair_right p q) (le_pair_right t _)
  have hnp : n + p ≤ M := le_trans (_root_.add_le_add le_rfl (ltl p q).le) hnM
  have hnq : n + q ≤ M := le_trans (_root_.add_le_add le_rfl (ltr p q).le) hnM
  have hcM : cop p q ≤ M := le_trans le_add_self hnM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih₁ hnp)
  obtain ⟨F₃, hF₃l, hF₃⟩ := typed_of_ΘB hq (ih₂ hnq)
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪t, p, q⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lF₃ : F₃.val ≤ lvB (Gd M ⟪t, p, q⟫) := lift_lvB hF₃l (Gd_mono M hqx)
  have lMax : (MaxT F₁ F₃).val ≤ lvB (Gd M (cop p q)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lF₃) (by rw [hx1]; exact Gd_grow M _)
  have hxM : ⟪t, p, q⟫ ≤ M := le_trans (show ⟪t, p, q⟫ ≤ cop p q from hx1 p q ▸ le_self_add) hcM
  have lP₀ : (envFormT n hp).val ≤ lvB (uD M) := lift_lvB (envF_le hp hnp) (A0_le_uD M)
  have lP₂ : (envFormT n hq).val ≤ lvB (uD M) := lift_lvB (envF_le hq hnq) (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀ (lift_lvB lF₁ (Gd_le_uD hxM)) lP₂
    (lift_lvB lF₃ (Gd_le_uD hxM))
    ((henv hp hq).trans_le (lift_lvB (envF_le (hsem hp hq) hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := step hu hK (wD_le_W M ⟪t, p, q⟫) (hF₁.mono (upW M _ _ hpx))
    (hF₃.mono (upW M _ _ hqx))
  exact ΘB_of_typed _ (henv hp hq) _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

theorem case_and (M : V) :
    ∀ n p q, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
    ΘB (Ad M) Kd (Wd M + 60) M n p → ΘB (Ad M) Kd (Wd M + 60) M n q →
    ΘB (Ad M) Kd (Wd M + 60) M n (p ^⋏ q) :=
  case_bin M (cop := (· ^⋏ ·)) (t := 4) (fun _ _ => rfl) (· ⋏ ·) and_step_le lt_K!_left
    lt_K!_right (fun hp hq => by simp [hp, hq])
    (fun hp hq => by simp [envFormT, envForm_and hp.isUFormula hq.isUFormula])

theorem case_or (M : V) :
    ∀ n p q, IsSemiformula ℒₛₑₜ n p → IsSemiformula ℒₛₑₜ n q →
    ΘB (Ad M) Kd (Wd M + 60) M n p → ΘB (Ad M) Kd (Wd M + 60) M n q →
    ΘB (Ad M) Kd (Wd M + 60) M n (p ^⋎ q) :=
  case_bin M (cop := (· ^⋎ ·)) (t := 5) (fun _ _ => rfl) (· ⋎ ·) or_step_le lt_or_left
    lt_or_right (fun hp hq => by simp [hp, hq])
    (fun hp hq => by simp [envFormT, envForm_or hp.isUFormula hq.isUFormula])

end LeanProofs.ZFCinPA.SizedDriver
