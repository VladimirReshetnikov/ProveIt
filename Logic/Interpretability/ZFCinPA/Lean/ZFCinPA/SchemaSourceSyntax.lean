import ZFCinPA.OpenSchemaTemplates
import ZFCinPA.SubstIdentity
import ZFCinPA.LTemplate

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

/-- The separation witness matrix `u ∈ &0 ∧ v = u ∧ R u`. -/
def sepMat : Semiproposition SL 2 :=
  Semiformula.rel Language.Mem.mem ![#0, &0] ⋏
    (Semiformula.rel Language.Eq.eq ![#1, #0] ⋏ (Rewriting.emb R1 ⇜ ![(#0 : SyntacticSemiterm SL 2)]))

/-- The replacement witness matrix, guarded by the supplied domain. -/
def repMat (δ : SetTheorySemisentence 1) : Semiproposition RL 2 :=
  Semiformula.rel Language.Mem.mem ![#0, &0] ⋏
    ((Rew.embSubsts ![(#1 : SyntacticSemiterm RL 2)] ▹ liftSet δ) ⋏
      (Rewriting.emb R2 ⇜ ![(#0 : SyntacticSemiterm RL 2), #1]))

/-- Evaluate the replacement witness matrix in a template structure. -/
theorem eval_repMat {M : Type} [Nonempty M] [SetStructure M]
    [s : Structure RL M] [Structure.Eq RL M] [Structure.Mem RL M]
    (δ : SetTheorySemisentence 1) (f : ℕ → M) (u v : M) :
    (repMat δ).Eval ![u, v] f ↔ u ∈ f 0 ∧ δ.Eval ![v] Empty.elim ∧
      Structure.rel (L := RL) (placeholderRel 0) ![u, v] := by
  simp only [repMat, R2, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_embSubsts, liftSet, LTemplate.eval_set_lMap]
  simp

/-- Construct a separation witness from the GIC matrix bounds. -/
theorem separation_witness {M : Type*} (mem : M → M → Prop) (D : M → Prop)
    (E : M → M → Prop) (R : M → Prop) {x b : M}
    (member_domain : ∀ {y z}, D z → mem y z → D y)
    (domain_closed : ∀ {z}, (∀ y, mem y z → D y) → D z)
    (symm : ∀ {u v}, E u v → E v u)
    (cong : ∀ u v, D u → D v → E u v → R u → R v)
    (hx : D x) (hb1 : ∀ y, mem y b → mem y x ∧ R y)
    (hb2 : ∀ u, mem u x → R u → mem u b) :
    D b ∧ ∀ z, D z →
      ((∃ v, mem v b ∧ E z v) ↔ (∃ u, mem u x ∧ E z u) ∧ R z) := by
  have hbD : ∀ v, mem v b → D v := fun v hv ↦ member_domain hx (hb1 v hv).1
  refine ⟨domain_closed hbD, fun z hz ↦ ?_⟩
  constructor
  · rintro ⟨v, hv, hzv⟩
    obtain ⟨hu, hR⟩ := hb1 v hv
    exact ⟨⟨v, hu, hzv⟩, cong v z (member_domain hx hu) hz (symm hzv) hR⟩
  · rintro ⟨⟨u, hu, hzu⟩, hR⟩
    have hRu := cong z u hz (member_domain hx hu) hzu hR
    exact ⟨u, hb2 u hu hRu, hzu⟩

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
