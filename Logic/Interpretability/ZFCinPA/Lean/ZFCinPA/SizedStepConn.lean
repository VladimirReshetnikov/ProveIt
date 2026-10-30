import ZFCinPA.SizedDriverLevels

/-!
# Bounded driver steps: `∧` and `∨`

`and_step_le` and `or_step_le`, the bounded twins of
`LDriverSteps.and_step` and `LDriverSteps.or_step`.

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


/-! ## The bounded steps -/

set_option maxHeartbeats 4000000 in
/-- The `∧` (`isAnd = true`) and `∨` steps: the templates differ, the derivation chain
after normalization is shared. -/
theorem conn_step_le (isAnd : Bool) {P₀ P₂ : SF V 1} {F₁ F₃ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ P₂ F₃ (cond isAnd (P₀ ⋏ P₂) (P₀ ⋎ P₂)) (MaxT F₁ F₃) i).val ≤ lvB u)
    (hw : wD u ≤ w) (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w)
    (h₃ : DLv 𝗭𝗙 (insert (InvT P₂ F₃).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (cond isAnd (P₀ ⋏ P₂) (P₀ ⋎ P₂)) (MaxT F₁ F₃)).val ∅) (w + 30) := by
  have hw4 := wD_4 hw
  have hmI := wD_m hw
  obtain ⟨up, u4, uA⟩ := wD_up hw
  cases isAnd
  case' true =>
      simp only [cond_true] at hK ⊢
      have hc := compiledLe (by decide) andTemplate_provable _ hu hK
      have lt := trD_le andTemplate tD_and _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 P₀ F₁ P₂ F₃ (P₀ ⋏ P₂) (MaxT F₁ F₃))
            (Rewriting.emb andTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [andTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
        tr_tot₃, tr_refl₂₃, tr_andDefP, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pA := dall_iff (P₀ ⋏ P₂) (hK 4) hu
      have hcl := c_and_le u
  case' false =>
      simp only [cond_false] at hK ⊢
      have hc := compiledLe (by decide) orTemplate_provable _ hu hK
      have lt := trD_le orTemplate tD_or _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 P₀ F₁ P₂ F₃ (P₀ ⋎ P₂) (MaxT F₁ F₃))
            (Rewriting.emb orTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [orTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
        tr_tot₃, tr_refl₂₃, tr_orDefP, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pA := dall_iff (P₀ ⋎ P₂) (hK 4) hu
      have hcl := c_or_le u
  all_goals
    have hA := imp_ante_le lt
    have hA2 := and_right_le hA
    have hA3 := and_right_le hA2
    have hA4 := and_right_le hA3
    have hA5 := and_right_le hA4
    have l0 := invT_le (P := P₀) (F := F₁) hu (hK 0) (hK 1)
    have l2 := invT_le (P := P₂) (F := F₃) hu (hK 2) (hK 3)
    have t1 := dleftW hw4 l0 hmI h₁ le_rfl
    have r1 := drightW hw4 l0 hmI h₁ le_rfl
    have t3 := dleftW hw4 l2 hmI h₃ le_rfl
    have r3 := drightW hw4 l2 hmI h₃ le_rfl
    have pF := dall2_swap (MaxT F₁ F₃) (hK 5) hu
    have c5 := dandW (u4 3) hA5 (uA 3) pA (le_trans (wD_i hw) (up 3)) pF (le_trans (wD_s hw) (up 3))
    have c4 := dandW (u4 5) hA4 (uA 5) r3 (le_of_add_eq (y := 2) (by ring)) c5 (le_of_eq (by ring))
    have c3 := dandW (u4 7) hA3 (uA 7) t3 (le_of_add_eq (y := 4) (by ring)) c4 (le_of_eq (by ring))
    have c2 := dandW (u4 9) hA2 (uA 9) r1 (le_of_add_eq (y := 6) (by ring)) c3 (le_of_eq (by ring))
    have c1 := dandW (u4 11) hA (uA 11) t1 (le_of_add_eq (y := 8) (by ring)) c2 (le_of_eq (by ring))
    have d := dmpW (u4 13) lt (uA 13) hc (le_trans (le_trans hcl (wD_c hw)) (up 13)) c1
      (le_of_eq (by ring))
    exact d.mono (le_of_add_eq (y := 14) (by ring))

theorem and_step_le {P₀ P₂ : SF V 1} {F₁ F₃ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ P₂ F₃ (P₀ ⋏ P₂) (MaxT F₁ F₃) i).val ≤ lvB u) (hw : wD u ≤ w)
    (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) (h₃ : DLv 𝗭𝗙 (insert (InvT P₂ F₃).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (P₀ ⋏ P₂) (MaxT F₁ F₃)).val ∅) (w + 30) :=
  conn_step_le true hu hK hw h₁ h₃

theorem or_step_le {P₀ P₂ : SF V 1} {F₁ F₃ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ P₂ F₃ (P₀ ⋎ P₂) (MaxT F₁ F₃) i).val ≤ lvB u) (hw : wD u ≤ w)
    (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) (h₃ : DLv 𝗭𝗙 (insert (InvT P₂ F₃).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (P₀ ⋎ P₂) (MaxT F₁ F₃)).val ∅) (w + 30) :=
  conn_step_le false hu hK hw h₁ h₃

end LeanProofs.ZFCinPA.SizedDriverSteps
