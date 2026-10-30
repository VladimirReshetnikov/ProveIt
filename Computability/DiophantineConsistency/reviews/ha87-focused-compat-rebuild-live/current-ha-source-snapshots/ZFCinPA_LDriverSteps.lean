import ZFCinPA.LNumOK

set_option autoImplicit false
noncomputable section

/-!
# The compiled steps of the `hSchema` driver

Each step template of the reflection generator, compiled at internal codes
(`LTemplate.compileT_provable`) and put in closed form with `LDriverBase`'s
translation lemmas. The new function code of every step is chosen as the
translation of the template's own defining matrix, so each definitional
hypothesis becomes the internal tautology `∀(A ↔ A)` and only the genuine
premises remain:

* `and_step`, `or_step`: `InvT P₀ F₁ → InvT P₂ F₃ → InvT (P₀ ∘ P₂) (MaxT F₁ F₃)`;
* `neg_step`: `InvT P F → InvT (∼P) F`;
* `top_base`, `bot_base`: `InvT ⊤ succT`, `InvT ⊥ succT`;
* `atom_step`: numeral premises (`LNumOK.numOK`) give `InvT (AtomT …) succT`;
* `ex_step`, `all_step`: `InvT P F → InvT (ExT P) (MaxT F (WbT P))` and the
  universal dual.
-/

namespace LeanProofs.ZFCinPA.LDriverSteps

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic
open LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT LeanProofs.ZFCinPA.LDriverBase

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


theorem tr_and' (Ks : (i : Fin 6) → SF V (ar6 i)) {n : ℕ} (p q : Semiproposition L6 n) :
    translateFormula Ks (p ⋏ q) = translateFormula Ks p ⋏ translateFormula Ks q := rfl

/-- A step template, compiled at a placeholder tuple. -/
theorem compiled {σ : Sentence L6} (h : templTheory 6 ar6 ⊢ σ) (Ks : (i : Fin 6) → SF V (ar6 i)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula Ks (Rewriting.emb σ) :=
  compileT_provable (by decide) Ks h

/-- The successor function code. -/
def succT : SF V 2 := ⌜succP⌝

theorem and_step (P₀' P₂' : SF V 1) (F₁' F₃' : SF V 2)
    (h₁ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₀' F₁') (h₃ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₂' F₃') :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (P₀' ⋏ P₂') (MaxT F₁' F₃') := by
  have hc := compiled andTemplate_provable (K6 P₀' F₁' P₂' F₃' (P₀' ⋏ P₂') (MaxT F₁' F₃'))
  simp only [andTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_tot₃, tr_refl₂₃, tr_andDefP, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (K!_left h₁) (K!_intro (K!_right h₁) (K!_intro (K!_left h₃)
    (K!_intro (K!_right h₃) (K!_intro (all_iff_self _) (all₂_iff_self _)))))

theorem or_step (P₀' P₂' : SF V 1) (F₁' F₃' : SF V 2)
    (h₁ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₀' F₁') (h₃ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₂' F₃') :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (P₀' ⋎ P₂') (MaxT F₁' F₃') := by
  have hc := compiled orTemplate_provable (K6 P₀' F₁' P₂' F₃' (P₀' ⋎ P₂') (MaxT F₁' F₃'))
  simp only [orTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_tot₃, tr_refl₂₃, tr_orDefP, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (K!_left h₁) (K!_intro (K!_right h₁) (K!_intro (K!_left h₃)
    (K!_intro (K!_right h₃) (K!_intro (all_iff_self _) (all₂_iff_self _)))))

theorem neg_step (P₀' : SF V 1) (F₁' : SF V 2) (h₁ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₀' F₁') :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (∼P₀') F₁' := by
  have hc := compiled negTemplate_provable (K6 P₀' F₁' ⊤ ⊤ (∼P₀') F₁')
  simp only [negTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_negDefP, tr_eqDefF, tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (K!_left h₁) (K!_intro (K!_right h₁)
    (K!_intro (all_iff_self _) (all₂_iff_self _)))

theorem top_base : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (⊤ : SF V 1) succT := by
  have hc := compiled topBase_provable (K6 ⊤ ⊤ ⊤ ⊤ ⊤ (succT (V := V)))
  simp only [topBase, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_topDefP, tr_succDefF,
    tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (all_iff_self _) (all₂_iff_self _)

theorem bot_base : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (⊥ : SF V 1) succT := by
  have hc := compiled botBase_provable (K6 ⊤ ⊤ ⊤ ⊤ ⊥ (succT (V := V)))
  simp only [botBase, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_botDefP, tr_succDefF,
    tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (all_iff_self _) (all₂_iff_self _)

theorem atom_step (isEq : Bool) (N₀ N₂ : SF V 1) (h₀ : (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT N₀) (h₂ : (𝗭𝗙 : SetTheory).internalize V ⊢ NumOKT N₂) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (AtomT isEq N₀ N₂) succT := by
  cases isEq with
  | false =>
      have hc := compiled (atomTemplate_provable false)
        (K6 N₀ ⊤ N₂ ⊤ (AtomT false N₀ N₂) (succT (V := V)))
      simp only [memAtomTemplate, Bool.false_eq_true, if_false,
        LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
        translateFormula_imp, tr_and', tr_numOK₀, tr_numOK₂, tr_memAtomDefP, tr_succDefF,
        tr_tot₅, tr_refl₄₅] at hc
      exact hc ⨀ K!_intro h₀ (K!_intro h₂ (K!_intro (all_iff_self _) (all₂_iff_self _)))
  | true =>
      have hc := compiled (atomTemplate_provable true)
        (K6 N₀ ⊤ N₂ ⊤ (AtomT true N₀ N₂) (succT (V := V)))
      simp only [eqAtomTemplate, if_true,
        LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
        translateFormula_imp, tr_and', tr_numOK₀, tr_numOK₂, tr_eqAtomDefP, tr_succDefF,
        tr_tot₅, tr_refl₄₅] at hc
      exact hc ⨀ K!_intro h₀ (K!_intro h₂ (K!_intro (all_iff_self _) (all₂_iff_self _)))

theorem ex_step (P₀' : SF V 1) (F₁' : SF V 2) (h₁ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₀' F₁') :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (ExT P₀') (MaxT F₁' (WbT P₀')) := by
  have hc := compiled exTemplate_provable
    (K6 P₀' F₁' ⊤ (WbT P₀') (ExT P₀') (MaxT F₁' (WbT P₀')))
  simp only [exTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_exDefP, tr_wbDef₀, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (K!_left h₁) (K!_intro (K!_right h₁)
    (K!_intro (all_iff_self _) (K!_intro (all₂_iff_self _) (all₂_iff_self _))))

theorem all_step (P₀' : SF V 1) (F₁' : SF V 2) (h₁ : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P₀' F₁') :
    (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (AllT P₀') (MaxT F₁' (WbNT P₀')) := by
  have hc := compiled allTemplate_provable
    (K6 P₀' F₁' ⊤ (WbNT P₀') (AllT P₀') (MaxT F₁' (WbNT P₀')))
  simp only [allTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_and', tr_tot₁, tr_refl₀₁,
    tr_allDefP, tr_wbDefN, tr_maxDefF, tr_tot₅, tr_refl₄₅] at hc
  exact hc ⨀ K!_intro (K!_left h₁) (K!_intro (K!_right h₁)
    (K!_intro (all_iff_self _) (K!_intro (all₂_iff_self _) (all₂_iff_self _))))

end LeanProofs.ZFCinPA.LDriverSteps
