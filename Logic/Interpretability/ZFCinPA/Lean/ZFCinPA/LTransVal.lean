import ZFCinPA.LTemplate

set_option autoImplicit false
noncomputable section

/-!
# Translated template codes are `Σ₁` in the placeholder codes

The `hSchema` generator proves statements of the form "`𝗭𝗙` proves the
translation of a fixed template sentence at internal formula codes" by
internal induction, so the code of a translation must be a `Σ₁`-definable
function of the placeholder codes. `transVal vals p` is the untyped mirror of
`SetPlaceholders.translateFormula` on code values (`val_translateFormula`);
its definability (`transVal_definable`) is proved once, by induction on the
fixed source formula: every clause is a qq-constructor, `subst`, or `neg`
applied to definable functions, and the translated term vectors are constant
parameters.
-/

namespace LeanProofs.ZFCinPA.LTransVal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {arities : Fin k → ℕ}

/-- The untyped mirror of `translateFormula`, on code values. -/
noncomputable def transVal (vals : Fin k → V) :
    {n : ℕ} → Semiproposition (setTemplateLanguage k arities) n → V
  | _, ⊤ => ^⊤
  | _, ⊥ => ^⊥
  | n, .rel (Sum.inl r) v =>
      (Bootstrapping.Semiformula.rel r (fun i ↦ translateTerm (V := V) (v i)) :
        Bootstrapping.Semiformula V ℒₛₑₜ n).val
  | _, .rel (Sum.inr r) v =>
      Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val fun j ↦ translateTerm (V := V) (v (Fin.cast r.2 j)))
        (vals r.1)
  | n, .nrel (Sum.inl r) v =>
      (Bootstrapping.Semiformula.nrel r (fun i ↦ translateTerm (V := V) (v i)) :
        Bootstrapping.Semiformula V ℒₛₑₜ n).val
  | _, .nrel (Sum.inr r) v =>
      neg ℒₛₑₜ (Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val fun j ↦ translateTerm (V := V) (v (Fin.cast r.2 j)))
        (vals r.1))
  | _, p ⋏ q => transVal vals p ^⋏ transVal vals q
  | _, p ⋎ q => transVal vals p ^⋎ transVal vals q
  | _, ∀⁰ p => ^∀ transVal vals p
  | _, ∃⁰ p => ^∃ transVal vals p

/-- The code of a translation is `transVal` of the placeholder codes. -/
theorem val_translateFormula
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    ∀ {n : ℕ} (p : Semiproposition (setTemplateLanguage k arities) n),
      (translateFormula Ks p).val = transVal (fun i ↦ (Ks i).val) p
  | _, ⊤ => rfl
  | _, ⊥ => rfl
  | _, .rel (Sum.inl _) _ => rfl
  | _, .rel (Sum.inr _) _ => rfl
  | _, .nrel (Sum.inl _) _ => rfl
  | _, .nrel (Sum.inr _) _ => rfl
  | _, p ⋏ q => by
      simp only [translateFormula, transVal, Bootstrapping.Semiformula.val_and,
        val_translateFormula Ks p, val_translateFormula Ks q]
  | _, p ⋎ q => by
      simp only [translateFormula, transVal, Bootstrapping.Semiformula.val_or,
        val_translateFormula Ks p, val_translateFormula Ks q]
  | _, ∀⁰ p => by
      simp only [translateFormula, transVal, Bootstrapping.Semiformula.val_all,
        val_translateFormula Ks p]
  | _, ∃⁰ p => by
      simp only [translateFormula, transVal, Bootstrapping.Semiformula.val_exs,
        val_translateFormula Ks p]

/-- **`transVal` is `Σ₁` in the placeholder codes**, for every fixed source
formula. -/
theorem transVal_definable :
    ∀ {n : ℕ} (p : Semiproposition (setTemplateLanguage k arities) n),
      𝚺₁.DefinableFunction (fun vals : Fin k → V ↦ transVal vals p)
  | _, ⊤ => HierarchySymbol.DefinableFunction.const (^⊤ : V)
  | _, ⊥ => HierarchySymbol.DefinableFunction.const (^⊥ : V)
  | _, .rel (Sum.inl _) _ => HierarchySymbol.DefinableFunction.const _
  | _, .rel (Sum.inr r) _ =>
      HierarchySymbol.DefinableFunction₂.comp (F := Bootstrapping.subst ℒₛₑₜ)
        (HierarchySymbol.DefinableFunction.const _) (HierarchySymbol.DefinableFunction.var r.1)
  | _, .nrel (Sum.inl _) _ => HierarchySymbol.DefinableFunction.const _
  | _, .nrel (Sum.inr r) _ =>
      HierarchySymbol.DefinableFunction₁.comp (F := neg ℒₛₑₜ)
        (HierarchySymbol.DefinableFunction₂.comp (F := Bootstrapping.subst ℒₛₑₜ)
          (HierarchySymbol.DefinableFunction.const _) (HierarchySymbol.DefinableFunction.var r.1))
  | _, p ⋏ q =>
      HierarchySymbol.DefinableFunction₂.comp (F := qqAnd)
        (transVal_definable p) (transVal_definable q)
  | _, p ⋎ q =>
      HierarchySymbol.DefinableFunction₂.comp (F := qqOr)
        (transVal_definable p) (transVal_definable q)
  | _, ∀⁰ p =>
      HierarchySymbol.DefinableFunction₁.comp (F := qqAll) (transVal_definable p)
  | _, ∃⁰ p =>
      HierarchySymbol.DefinableFunction₁.comp (F := qqExs) (transVal_definable p)

end LeanProofs.ZFCinPA.LTransVal
