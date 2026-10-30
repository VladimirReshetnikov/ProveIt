import ZFCinPA.SizedDriverLevels

/-!
# Bounded driver steps: `¬`, `⊤`, `⊥`

`neg_step_le` and `base_step_le` (`⊤`, `⊥`).

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
theorem neg_step_le {P₀ : SF V 1} {F₁ : SF V 2} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 P₀ F₁ ⊤ ⊤ (∼P₀) F₁ i).val ≤ lvB u) (hw : wD u ≤ w)
    (h₁ : DLv 𝗭𝗙 (insert (InvT P₀ F₁).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (∼P₀) F₁).val ∅) (w + 30) := by
  obtain ⟨up, u4, uA⟩ := wD_up hw
  have hc := compiledLe (by decide) negTemplate_provable _ hu hK
  have lt := trD_le negTemplate tD_neg _ hK
  obtain ⟨T, hT⟩ : ∃ T,
      translateFormula (K6 P₀ F₁ ⊤ ⊤ (∼P₀) F₁)
        (Rewriting.emb negTemplate) = T :=
    ⟨_, rfl⟩
  rw [hT] at hc lt
  simp only [negTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_negDefP, tr_eqDefF, tr_tot₅, tr_refl₄₅] at hT
  subst hT
  have hA := imp_ante_le lt
  have hA2 := and_right_le hA
  have hA3 := and_right_le hA2
  obtain ⟨t1, r1⟩ := inv_halves (P := P₀) (F := F₁) hu hw (hK 0) (hK 1) h₁
  have pA := dall_iff (∼P₀) (hK 4) hu
  have pF := dall2_swap F₁ (hK 5) hu
  have c3 := dandW (u4 3) hA3 (uA 3) pA (le_trans (wD_i hw) (up 3)) pF (le_trans (wD_s hw) (up 3))
  have c2 := dandW (u4 5) hA2 (uA 5) r1 (le_of_add_eq (y := 2) (by ring)) c3 (le_of_eq (by ring))
  have c1 := dandW (u4 7) hA (uA 7) t1 (le_of_add_eq (y := 4) (by ring)) c2 (le_of_eq (by ring))
  have d := dmpW (u4 9) lt (uA 9) hc (le_trans (le_trans (c_neg_le u) (wD_c hw)) (up 9)) c1
    (le_of_eq (by ring))
  exact d.mono (le_of_add_eq (y := 18) (by ring))

set_option maxHeartbeats 4000000 in
/-- The `⊤` (`isTop = true`) and `⊥` base cases. -/
theorem base_step_le (isTop : Bool) {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 ⊤ ⊤ ⊤ ⊤ (cond isTop ⊤ ⊥) (succT (V := V)) i).val ≤ lvB u) (hw : wD u ≤ w) :
    DLv 𝗭𝗙 (insert (InvT (cond isTop ⊤ ⊥ : SF V 1) succT).val ∅) (w + 30) := by
  obtain ⟨up, u4, uA⟩ := wD_up hw
  cases isTop
  case' true =>
      simp only [cond_true] at hK ⊢
      have hc := compiledLe (by decide) topBase_provable _ hu hK
      have lt := trD_le topBase tD_top _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 ⊤ ⊤ ⊤ ⊤ ⊤ (succT (V := V))) (Rewriting.emb topBase) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [topBase, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_topDefP, tr_succDefF,
        tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pA := dall_iff (⊤ : SF V 1) (hK 4) hu
      have hcl := c_top_le u
  case' false =>
      simp only [cond_false] at hK ⊢
      have hc := compiledLe (by decide) botBase_provable _ hu hK
      have lt := trD_le botBase tD_bot _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 ⊤ ⊤ ⊤ ⊤ ⊥ (succT (V := V))) (Rewriting.emb botBase) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [botBase, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_botDefP, tr_succDefF,
        tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have pA := dall_iff (⊥ : SF V 1) (hK 4) hu
      have hcl := c_bot_le u
  all_goals
    have c1 := dandW (u4 0) (imp_ante_le lt) (uA 0) pA (le_trans (wD_i hw) (up 0))
      (dall2_swap (succT (V := V)) (hK 5) hu) (le_trans (wD_s hw) (up 0))
    exact (dmpW (u4 2) lt (uA 2) hc (le_trans (le_trans hcl (wD_c hw)) (up 2)) c1
      (le_of_eq (by ring))).mono (le_of_add_eq (y := 25) (by ring))

end LeanProofs.ZFCinPA.SizedDriverSteps
