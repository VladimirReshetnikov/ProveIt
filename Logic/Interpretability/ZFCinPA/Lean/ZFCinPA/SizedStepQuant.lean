import ZFCinPA.SizedDriverLevels

/-!
# Bounded driver steps: `∃` and `∀`

`ex_step_le` and `all_step_le`.

Part of the bounded `hSchema` driver (`SizedDriver`), split out of one
module so that each Lean process elaborates only a few step proofs.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriverSteps

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq fvar0_le)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le)
open LeanProofs.ZFCinPA.SizedLPlumbing LeanProofs.ZFCinPA.SizedLGlue1 LeanProofs.ZFCinPA.SizedLNumOK
open LeanProofs.ZFCinPA.SizedLSlot (tsubst_le_n)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ


set_option maxHeartbeats 4000000 in
/-- The `∃` (`isEx = true`) and `∀` steps: the templates differ, the derivation chain
after normalization is shared. -/
theorem quant_step_le (isEx : Bool) {P₀ : SF V 1} {F₁ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ ⊤ (cond isEx (WbT P₀) (WbNT P₀)) (cond isEx (ExT P₀) (AllT P₀))
      (MaxT F₁ (cond isEx (WbT P₀) (WbNT P₀))) i).val ≤ lvB u)
    (hw : wD u ≤ w) (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (cond isEx (ExT P₀) (AllT P₀)) (MaxT F₁ (cond isEx (WbT P₀) (WbNT P₀)))).val ∅)
      (w + 30) := by
  have hw4 := wD_4 hw
  have hmI := wD_m hw
  obtain ⟨up, u4, uA⟩ := wD_up hw
  cases isEx
  case' true =>
      simp only [cond_true] at hK ⊢
      have hc := compiledLe (by decide) exTemplate_provable _ hu hK
      have lt := trD_le exTemplate tD_ex _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 P₀ F₁ ⊤ (WbT P₀) (ExT P₀) (MaxT F₁ (WbT P₀)))
            (Rewriting.emb exTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [exTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
        tr_exDefP, tr_wbDef₀, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pE := dall_iff (ExT P₀) (hK 4) hu
      have pW := dall2_iff (WbT P₀) (hK 3) hu
      have pM := dall2_swap (MaxT F₁ (WbT P₀)) (hK 5) hu
      have hcl := c_ex_le u
  case' false =>
      simp only [cond_false] at hK ⊢
      have hc := compiledLe (by decide) allTemplate_provable _ hu hK
      have lt := trD_le allTemplate tD_all _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 P₀ F₁ ⊤ (WbNT P₀) (AllT P₀) (MaxT F₁ (WbNT P₀)))
            (Rewriting.emb allTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [allTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
        tr_allDefP, tr_wbDefN, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pE := dall_iff (AllT P₀) (hK 4) hu
      have pW := dall2_iff (WbNT P₀) (hK 3) hu
      have pM := dall2_swap (MaxT F₁ (WbNT P₀)) (hK 5) hu
      have hcl := c_all_le u
  all_goals
    have hA := imp_ante_le lt
    have hA2 := and_right_le hA
    have hA3 := and_right_le hA2
    have hA4 := and_right_le hA3
    have l0 := invT_le (P := P₀) (F := F₁) hu (hK 0) (hK 1)
    have t1 := dleftW hw4 l0 hmI h₁ le_rfl
    have r1 := drightW hw4 l0 hmI h₁ le_rfl
    have c4 := dandW (u4 3) hA4 (uA 3) pW (le_trans (wD_a hw) (up 3)) pM (le_trans (wD_s hw) (up 3))
    have c3 := dandW (u4 5) hA3 (uA 5) pE (le_trans (wD_i hw) (up 5)) c4 (le_of_eq (by ring))
    have c2 := dandW (u4 7) hA2 (uA 7) r1 (le_of_add_eq (y := 4) (by ring)) c3 (le_of_eq (by ring))
    have c1 := dandW (u4 9) hA (uA 9) t1 (le_of_add_eq (y := 6) (by ring)) c2 (le_of_eq (by ring))
    have d := dmpW (u4 11) lt (uA 11) hc (le_trans (le_trans hcl (wD_c hw)) (up 11)) c1
      (le_of_eq (by ring))
    exact d.mono (le_of_add_eq (y := 16) (by ring))

theorem ex_step_le {P₀ : SF V 1} {F₁ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ ⊤ (WbT P₀) (ExT P₀) (MaxT F₁ (WbT P₀)) i).val ≤ lvB u) (hw : wD u ≤ w)
    (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (ExT P₀) (MaxT F₁ (WbT P₀))).val ∅) (w + 30) :=
  quant_step_le true hu hK hw h₁

theorem all_step_le {P₀ : SF V 1} {F₁ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ ⊤ (WbNT P₀) (AllT P₀) (MaxT F₁ (WbNT P₀)) i).val ≤ lvB u)
    (hw : wD u ≤ w) (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (AllT P₀) (MaxT F₁ (WbNT P₀))).val ∅) (w + 30) :=
  quant_step_le false hu hK hw h₁

end LeanProofs.ZFCinPA.SizedDriverSteps
