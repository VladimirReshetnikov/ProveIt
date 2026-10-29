import ZFCinPA.OpenSchemaTemplates
import ZFCinPA.SubstIdentity

set_option autoImplicit false
noncomputable section

/-! Common source syntax for the separation and replacement templates. -/

namespace LeanProofs.ZFCinPA.SchemaSourceSyntax

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSchemaTemplates
open scoped LO.FirstOrder.Arithmetic

local instance {k : ℕ} {arities : Fin k → ℕ} : Language.Mem (setTemplateLanguage k arities) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

abbrev ar1 : Fin 1 → ℕ := fun _ ↦ 1
abbrev SL := setTemplateLanguage 1 ar1

abbrev R1 : Semisentence SL 1 := .rel (placeholderRel (arities := ar1) 0) ![#0]
abbrev sepS : Sentence SL := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !R1 z”

abbrev ar2 : Fin 1 → ℕ := fun _ ↦ 2
abbrev RL := setTemplateLanguage 1 ar2

abbrev R2 : Semisentence RL 2 := .rel (placeholderRel (arities := ar2) 0) ![#0, #1]
abbrev repS : Sentence RL := “(∀ x, ∃! y, !R2 x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !R2 x y”

lemma emb_sepS : (Rewriting.emb sepS : Proposition SL) = sepBodySource (Rewriting.emb R1) := by
  simp [sepS, sepBodySource, R1]

lemma emb_repS : (Rewriting.emb repS : Proposition RL) = repBodySource (Rewriting.emb R2) := by
  simp [repS, repBodySource, R2, FirstOrder.Semiformula.existsUnique,
    FirstOrder.Semiformula.bexsMem, LO.FirstOrder.bexs]

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma subst_bvar0 (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (w : Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) (hw : w 0 = .bvar 0) :
    (K.subst w).val = K.val := by
  apply SubstIdentity.Semiformula.subst_bvarVec_val K w
  intro i
  rw [Fin.fin_one_eq_zero i, hw]
  rfl

lemma subst_bvar01 (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (w : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2) (hw0 : w 0 = .bvar 0) (hw1 : w 1 = .bvar 1) :
    (K.subst w).val = K.val := by
  apply SubstIdentity.Semiformula.subst_bvarVec_val K w
  intro i
  match i with
  | 0 => rw [hw0]; rfl
  | 1 => rw [hw1]; rfl

lemma translate_sepS (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    (translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb sepS : Proposition SL)).val =
      sepBodyVal K.val := by
  rw [emb_sepS, translate_sepBodySource]
  have e : translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb R1 : Semiproposition SL 1) = K :=
    Bootstrapping.Semiformula.ext (subst_bvar0 K _ rfl)
  rw [e, sepBodyVal_eq K]

lemma translate_repS (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb repS : Proposition RL)).val =
      repBodyVal K.val := by
  rw [emb_repS, translate_repBodySource]
  have e : translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb R2 : Semiproposition RL 2) = K :=
    Bootstrapping.Semiformula.ext (subst_bvar01 K _ rfl rfl)
  rw [e, repBodyVal_eq K]


end Internal

end LeanProofs.ZFCinPA.SchemaSourceSyntax
