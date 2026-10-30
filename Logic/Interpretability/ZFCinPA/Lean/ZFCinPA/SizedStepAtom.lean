import ZFCinPA.SizedDriverLevels

/-!
# Bounded driver step: atoms

`atom_step_le`, the bounded twin of `LDriverSteps.atom_step`.

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
theorem atom_step_le (isEq : Bool) {N₀ N₂ : SF V 1} {u w : V} (hu : 2 ≤ u)
    (hK : ∀ i, (K6 N₀ ⊤ N₂ ⊤ (AtomT isEq N₀ N₂) (succT (V := V)) i).val ≤ lvB u) (hw : wD u ≤ w)
    (h₀ : DLv 𝗭𝗙 (insert (NumOKT N₀).val ∅) w) (h₂ : DLv 𝗭𝗙 (insert (NumOKT N₂).val ∅) w) :
    DLv 𝗭𝗙 (insert (InvT (AtomT isEq N₀ N₂) succT).val ∅) (w + 30) := by
  have hw4 := wD_4 hw
  obtain ⟨up, u4, uA⟩ := wD_up hw
  have pA := dall_iff (AtomT isEq N₀ N₂) (hK 4) hu
  have pF := dall2_swap (succT (V := V)) (hK 5) hu
  cases isEq
  case' false =>
      have hc := compiledLe (by decide) memAtom_provable _ hu hK
      have lt := trD_le memAtomTemplate tD_mem _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 N₀ ⊤ N₂ ⊤ (AtomT false N₀ N₂) (succT (V := V)))
            (Rewriting.emb memAtomTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [memAtomTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_numOK₀, tr_numOK₂,
        tr_memAtomDefP, tr_succDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have hcl := c_mem_le u
  case' true =>
      have hc := compiledLe (by decide) eqAtom_provable _ hu hK
      have lt := trD_le eqAtomTemplate tD_eq _ hK
      obtain ⟨T, hT⟩ : ∃ T,
          translateFormula (K6 N₀ ⊤ N₂ ⊤ (AtomT true N₀ N₂) (succT (V := V)))
            (Rewriting.emb eqAtomTemplate) = T :=
        ⟨_, rfl⟩
      rw [hT] at hc lt
      simp only [eqAtomTemplate, LogicalConnective.HomClass.map_imply,
        LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_numOK₀, tr_numOK₂,
        tr_eqAtomDefP, tr_succDefF, tr_tot₅, tr_refl₄₅] at hT
      subst hT
      have hcl := c_eq_le u
  all_goals
    have hA := imp_ante_le lt
    have hA2 := and_right_le hA
    have hA3 := and_right_le hA2
    have c3 := dandW (u4 0) hA3 (uA 0) pA (le_trans (wD_i hw) (up 0)) pF
      (le_trans (wD_s hw) (up 0))
    have c2 := dandW (u4 2) hA2 (uA 2) h₂ (up 2) c3 (le_of_eq (by ring))
    have c1 := dandW (u4 4) hA (uA 4) h₀ (up 4) c2 (le_of_eq (by ring))
    have d := dmpW (u4 6) lt (uA 6) hc (le_trans (le_trans hcl (wD_c hw)) (up 6)) c1
      (le_of_eq (by ring))
    exact d.mono (le_of_add_eq (y := 21) (by ring))

end LeanProofs.ZFCinPA.SizedDriverSteps
