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
/-- **The quantifier case**, for a quantifier `Q` coded as `⟪t, p⟫ + 1` with witness
bound `Wb` and bounded invariant step `step`. -/
theorem case_quant (M : V) {cop : V → V} {t : V} (hx1 : ∀ p, cop p = ⟪t, p⟫ + 1)
    (Q : SF V 1 → SF V 1) (Wb : SF V 1 → SF V 2)
    (hWb : ∀ {P : SF V 1} {u : V}, 2 ≤ u → P.val ≤ lvB u → (Wb P).val ≤ lvB ((tB : V) * (u + 1)))
    (step : ∀ {P₀ : SF V 1} {F₁ : SF V 2} {u w : V}, 2 ≤ u →
      (∀ i, (K6 P₀ F₁ ⊤ (Wb P₀) (Q P₀) (MaxT F₁ (Wb P₀)) i).val ≤ lvB u) → wD u ≤ w →
      DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w →
      DLv 𝗭𝗙 (insert (InvT (Q P₀) (MaxT F₁ (Wb P₀))).val ∅) (w + 30))
    (hsem : ∀ {n p : V}, IsSemiformula ℒₛₑₜ (n + 1) p → IsSemiformula ℒₛₑₜ n (cop p))
    (hval : ∀ {n p : V} (hp : IsSemiformula ℒₛₑₜ (n + 1) p),
      (Q (envFormT (n + 1) hp)).val = envForm n (cop p)) :
    ∀ n p, IsSemiformula ℒₛₑₜ (n + 1) p → ΘB (Ad M) Kd (Wd M + 60) M (n + 1) p →
    ΘB (Ad M) Kd (Wd M + 60) M n (cop p) := by
  have hu := two_le_uD M
  unfold ΘB
  intro n p hp ih hnM
  have hpx : p ≤ ⟪t, p⟫ := le_pair_right t p
  have hnp : n + 1 + p ≤ M := le_trans (by
    rw [hx1, show n + 1 + p = n + (p + 1) by ring]
    exact _root_.add_le_add le_rfl (_root_.add_le_add hpx le_rfl)) hnM
  have hcM : cop p ≤ M := le_trans le_add_self hnM
  have hxM : ⟪t, p⟫ ≤ M := le_trans (show ⟪t, p⟫ ≤ cop p from hx1 p ▸ le_self_add) hcM
  obtain ⟨F₁, hF₁l, hF₁⟩ := typed_of_ΘB hp (ih hnp)
  have lP := envF_le hp hnp
  have lF₁ : F₁.val ≤ lvB (Gd M ⟪t, p⟫) := lift_lvB hF₁l (Gd_mono M hpx)
  have lW : (Wb (envFormT (n + 1) hp)).val ≤ lvB (Gd M ⟪t, p⟫) :=
    lift_lvB (hWb (two_le_A0 M) lP)
      (le_trans (le_trans le_self_add le_self_add) (Ad_le_Gd M _))
  have lMax : (MaxT F₁ (Wb (envFormT (n + 1) hp))).val ≤ lvB (Gd M (cop p)) :=
    lift_lvB (maxT_le (two_le_Gd M _) lF₁ lW) (by rw [hx1]; exact Gd_grow M _)
  have lP₀ : (envFormT (n + 1) hp).val ≤ lvB (uD M) := lift_lvB lP (A0_le_uD M)
  have hK := K6_le (u := uD M) lP₀ (lift_lvB lF₁ (Gd_le_uD hxM))
    (top_le hu) (lift_lvB lW (Gd_le_uD hxM))
    ((hval hp).trans_le (lift_lvB (envF_le (hsem hp) hnM) (A0_le_uD M)))
    (lift_lvB lMax (Gd_le_uD hcM))
  have d := step hu hK (wD_le_W M ⟪t, p⟫) (hF₁.mono (upW M _ _ hpx))
  exact ΘB_of_typed _ (hval hp) _ lMax
    (d.mono (by rw [hx1]; exact le_of_add_eq (y := 10) (by ring)))

theorem case_all (M : V) :
    ∀ n p, IsSemiformula ℒₛₑₜ (n + 1) p → ΘB (Ad M) Kd (Wd M + 60) M (n + 1) p →
    ΘB (Ad M) Kd (Wd M + 60) M n (^∀ p) :=
  case_quant M (cop := (^∀ ·)) (t := 6) (fun _ => rfl) AllT WbNT wbNT_le (quant_step_le false)
    (fun hp => by simp [hp]) (fun hp => by rw [allT_val, envForm_all hp.isUFormula]; rfl)

theorem case_exs (M : V) :
    ∀ n p, IsSemiformula ℒₛₑₜ (n + 1) p → ΘB (Ad M) Kd (Wd M + 60) M (n + 1) p →
    ΘB (Ad M) Kd (Wd M + 60) M n (^∃ p) :=
  case_quant M (cop := (^∃ ·)) (t := 7) (fun _ => rfl) ExT WbT wbT_le (quant_step_le true)
    (fun hp => by simp [hp]) (fun hp => by rw [exT_val, envForm_exs hp.isUFormula]; rfl)

end LeanProofs.ZFCinPA.SizedDriver
