import ZFCinPA.LInvariant

set_option autoImplicit false
noncomputable section

/-!
# The conjunction step of the reflection generator

The template sentence `andTemplate` over six placeholders
`P₀ F₁ P₂ F₃ P₄ F₅` (arities `1 2 1 2 1 2`) says: if `F₁`, `F₃` are total
reflection functions for `P₀`, `P₂` (`totS`, `reflS`), `P₄ = P₀ ∧ P₂` and
`F₅ = max(F₁, F₃)` (as the union of the two values), then `F₅` is a total
reflection function for `P₄`. It is a theorem of the template theory
(`andTemplate_provable`), proved semantically (`and_step`): a limit closed
under the maximum is closed under both components, and the internal
conjunction code `⟨4, ⟨c₁, c₂⟩⟩` reflects the conjunction by `satIn_and`.
-/

namespace LeanProofs.ZFCinPA.LStepAnd

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant

/-! ## Ordinal facts -/

section Ordinals

open SetTheory.BusyBeaver.ZFC.InternalOrd

variable {V : Type*} {mem : V → V → Prop} (H : _root_.SetTheory.ZFAxioms mem) (hR : Regular mem)
include H hR

/-- A nonzero ordinal contains `∅`. -/
lemma vempty_mem_of_ord {b : V} (hb : Ord mem b) (hne : ∃ x, mem x b) :
    mem (_root_.SetTheory.vempty H) b := by
  obtain ⟨m, hm, hmin⟩ := hR b hne
  have hm0 : m = _root_.SetTheory.vempty H :=
    H.ext _ _ fun z => ⟨fun hz => absurd ⟨z, hz, hb.1 m hm z hz⟩ hmin,
      fun hz => absurd hz (_root_.SetTheory.vempty_spec H z)⟩
  rwa [← hm0]

/-- The union of two ordinals is one of them. -/
lemma vcup_ord {g₁ g₂ : V} (h₁ : Ord mem g₁) (h₂ : Ord mem g₂) :
    _root_.SetTheory.vcup H g₁ g₂ = g₁ ∨ _root_.SetTheory.vcup H g₁ g₂ = g₂ := by
  rcases trichotomy H hR g₁ h₁ g₂ h₂ with h | rfl | h
  · right
    exact H.ext _ _ fun z => by
      rw [_root_.SetTheory.vcup_spec H g₁ g₂ z]
      exact ⟨fun hz => hz.elim (fun hz => h₂.1 g₁ h z hz) id, Or.inr⟩
  · left
    exact H.ext _ _ fun z => by
      rw [_root_.SetTheory.vcup_spec H g₁ g₁ z]; exact ⟨fun hz => hz.elim id id, Or.inl⟩
  · left
    exact H.ext _ _ fun z => by
      rw [_root_.SetTheory.vcup_spec H g₁ g₂ z]
      exact ⟨fun hz => hz.elim id (fun hz => h₁.1 g₂ h z hz), Or.inl⟩

/-- An ordinal contained in a member `g` of an ordinal `b` is a member of `b`. -/
lemma mem_of_sub_mem {g₁ g b : V} (hb : Ord mem b) (hg : mem g b) (h₁ : Ord mem g₁)
    (hsub : ∀ z, mem z g₁ → mem z g) : mem g₁ b := by
  have hgo : Ord mem g := ord_of_mem hb hg
  rcases trichotomy H hR g₁ h₁ g hgo with h | rfl | h
  · exact hb.1 g hg g₁ h
  · exact hg
  · exact absurd (hsub g h) (mem_irrefl H hR g)

end Ordinals

/-! ## The step, for arbitrary relations -/

section Step

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

/-- `F` is a total function on ordinals above its argument. -/
def Tot (F : V → V → Prop) : Prop :=
  ∀ a : V, Ord (memRel V) a → ∃ g, Ord (memRel V) g ∧ a ∈ g ∧ F a g ∧ ∀ h, F a h → h = g

/-- One code reflects `P` at every nonzero limit closed under `F`, for
environments over earlier stages. -/
def Refl (P : V → Prop) (F : V → V → Prop) : Prop :=
  ∃ c : V, IsFormCodeSem H c ∧
    ∀ b : V, IsLim (memRel V) b → (∀ a, a ∈ b → ∀ g, F a g → g ∈ b) →
      ∀ S, IsL H hP b S → ∀ R, MemRel H S R → ∀ a, a ∈ b → ∀ U, IsL H hP a U →
        ∀ t, IsEnvOn H U t → (P t ↔ SatIn H S R c t)

include hR in
/-- An environment over an earlier stage is an environment over the stage. -/
lemma envOn_stage {b S a U t : V} (hb : IsLim (memRel V) b) (hS : IsL H hP b S) (ha : a ∈ b)
    (hU : IsL H hP a U) (ht : IsEnvOn H U t) : IsEnvOn H S t :=
  ⟨ht.1, fun n y h => isL_mono H hR hP hb.1 ha hU hS y (ht.2 n y h)⟩

include hR in
/-- A nonzero limit stage with its membership relation is a set structure. -/
lemma isSetStructure_stage {b S R : V} (hb : IsLim (memRel V) b) (hS : IsL H hP b S)
    (hR' : MemRel H S R) : IsSetStructure H S R := by
  refine ⟨⟨_, ((isL_ord H hR hP b hb.1 S hS _).2 (vempty_mem_of_ord H hR hb.1 hb.2.1)).1⟩, ?_⟩
  intro p hp
  obtain ⟨x, y, hx, hy, -, rfl⟩ := (hR' p).1 hp
  exact ⟨x, y, hx, hy, rfl⟩

include hR in
/-- **The conjunction step.** -/
theorem and_step {P₀ P₂ P₄ : V → Prop} {F₁ F₃ F₅ : V → V → Prop}
    (htot₁ : Tot F₁) (hrefl₁ : Refl H hP P₀ F₁) (htot₃ : Tot F₃) (hrefl₃ : Refl H hP P₂ F₃)
    (hdefP : ∀ t, P₄ t ↔ P₀ t ∧ P₂ t)
    (hdefF : ∀ a g, F₅ a g ↔ ∃ g₁ g₂, F₁ a g₁ ∧ F₃ a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂) :
    Tot F₅ ∧ Refl H hP P₄ F₅ := by
  -- the maximum of the two components, at an ordinal
  have hmax : ∀ a, Ord (memRel V) a → ∃ g₁ g₂, F₁ a g₁ ∧ F₃ a g₂ ∧ Ord (memRel V) g₁ ∧
      Ord (memRel V) g₂ ∧ a ∈ g₁ ∧ F₅ a (_root_.SetTheory.vcup H g₁ g₂) := by
    intro a ha
    obtain ⟨g₁, ho₁, ha₁, hF₁, -⟩ := htot₁ a ha
    obtain ⟨g₂, ho₂, -, hF₃, -⟩ := htot₃ a ha
    exact ⟨g₁, g₂, hF₁, hF₃, ho₁, ho₂, ha₁,
      (hdefF a _).2 ⟨g₁, g₂, hF₁, hF₃, fun z => _root_.SetTheory.vcup_spec H g₁ g₂ z⟩⟩
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨g₁, g₂, hF₁, hF₃, ho₁, ho₂, ha₁, hF₅⟩ := hmax a ha
    refine ⟨_root_.SetTheory.vcup H g₁ g₂, ?_, ?_, hF₅, fun h hh => ?_⟩
    · rcases vcup_ord H hR ho₁ ho₂ with h | h <;> rw [h] <;> assumption
    · exact (_root_.SetTheory.vcup_spec H g₁ g₂ a).2 (Or.inl ha₁)
    · obtain ⟨g₁', g₂', hF₁', hF₃', hspec⟩ := (hdefF a h).1 hh
      obtain ⟨_, _, _, _, u₁⟩ := htot₁ a ha
      obtain ⟨_, _, _, _, u₃⟩ := htot₃ a ha
      have e₁ : g₁' = g₁ := (u₁ g₁' hF₁').trans (u₁ g₁ hF₁).symm
      have e₃ : g₂' = g₂ := (u₃ g₂' hF₃').trans (u₃ g₂ hF₃).symm
      subst e₁ e₃
      exact H.ext _ _ fun z => (hspec z).trans (_root_.SetTheory.vcup_spec H _ _ z).symm
  · obtain ⟨c₁, hc₁, hr₁⟩ := hrefl₁
    obtain ⟨c₂, hc₂, hr₂⟩ := hrefl₃
    refine ⟨_, isFormCodeSem_and H hc₁ hc₂, fun b hb hcl S hS R hR' a ha U hU t ht => ?_⟩
    -- closure under the maximum gives closure under both components
    have hcl' : ∀ a, a ∈ b → ∀ g₁ g₂, F₁ a g₁ → F₃ a g₂ → g₁ ∈ b ∧ g₂ ∈ b := by
      intro a ha g₁ g₂ hF₁ hF₃
      have hao : Ord (memRel V) a := ord_of_mem hb.1 ha
      obtain ⟨g₁', g₂', hF₁', hF₃', ho₁, ho₂, -, hF₅⟩ := hmax a hao
      obtain ⟨_, _, _, _, u₁⟩ := htot₁ a hao
      obtain ⟨_, _, _, _, u₃⟩ := htot₃ a hao
      have e₁ : g₁ = g₁' := (u₁ g₁ hF₁).trans (u₁ g₁' hF₁').symm
      have e₃ : g₂ = g₂' := (u₃ g₂ hF₃).trans (u₃ g₂' hF₃').symm
      subst e₁ e₃
      have hg := hcl a ha _ hF₅
      exact ⟨mem_of_sub_mem H hR hb.1 hg ho₁ fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz),
        mem_of_sub_mem H hR hb.1 hg ho₂ fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr hz)⟩
    have hcl₁ : ∀ a, a ∈ b → ∀ g, F₁ a g → g ∈ b := fun a ha g hg => by
      obtain ⟨g₂, -, -, hF₃, -⟩ := htot₃ a (ord_of_mem hb.1 ha)
      exact (hcl' a ha g g₂ hg hF₃).1
    have hcl₃ : ∀ a, a ∈ b → ∀ g, F₃ a g → g ∈ b := fun a ha g hg => by
      obtain ⟨g₁, -, -, hF₁, -⟩ := htot₁ a (ord_of_mem hb.1 ha)
      exact (hcl' a ha g₁ g hF₁ hg).2
    rw [hdefP, hr₁ b hb hcl₁ S hS R hR' a ha U hU t ht, hr₂ b hb hcl₃ S hS R hR' a ha U hU t ht,
      satIn_and H (isSetStructure_stage H hR hP hb hS hR') hc₁ hc₂
        (envOn_stage H hR hP hb hS ha hU ht)]

end Step

/-! ## The template sentence -/

/-- Placeholder arities: `P₀ F₁ P₂ F₃ P₄ F₅`. -/
abbrev ar6 : Fin 6 → ℕ := ![1, 2, 1, 2, 1, 2]

/-- The template language of the binary steps. -/
abbrev L6 := setTemplateLanguage 6 ar6

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

def P₀ : Semisentence L6 1 := .rel (placeholderRel (0 : Fin 6)) ![#0]
def F₁ : Semisentence L6 2 := .rel (placeholderRel (1 : Fin 6)) ![#0, #1]
def P₂ : Semisentence L6 1 := .rel (placeholderRel (2 : Fin 6)) ![#0]
def F₃ : Semisentence L6 2 := .rel (placeholderRel (3 : Fin 6)) ![#0, #1]
def P₄ : Semisentence L6 1 := .rel (placeholderRel (4 : Fin 6)) ![#0]
def F₅ : Semisentence L6 2 := .rel (placeholderRel (5 : Fin 6)) ![#0, #1]

/-- `P₄` is the conjunction of `P₀` and `P₂`. -/
def andDefP : Sentence L6 := “∀ t, !P₄ t ↔ !P₀ t ∧ !P₂ t”

/-- The maximum (union) of `F₁` and `F₃`, as a binary matrix. -/
def maxRHS : Semisentence L6 2 :=
  “a g. ∃ g₁, ∃ g₂, !F₁ a g₁ ∧ !F₃ a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂”

/-- `F₅` is the maximum (union) of `F₁` and `F₃`. The matrix is named so that,
at internal codes, choosing `F₅` to be the translation of `maxRHS` turns this
hypothesis into a literal tautology. -/
def maxDefF : Sentence L6 := “∀ a, ∀ g, !F₅ a g ↔ !maxRHS a g”

/-- **The conjunction template.** -/
def andTemplate : Sentence L6 :=
  (totS F₁ ⋏ reflS P₀ F₁ ⋏ totS F₃ ⋏ reflS P₂ F₃ ⋏ andDefP ⋏ maxDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

section Models

variable {M : Type} [Nonempty M] [SetStructure M]
variable [s : Structure L6 M] [Structure.Eq L6 M] [Structure.Mem L6 M]

omit [SetStructure M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
theorem models_andDefP :
    M↓[L6] ⊧ andDefP ↔ ∀ t : M, P₄.Eval ![t] Empty.elim ↔
      P₀.Eval ![t] Empty.elim ∧ P₂.Eval ![t] Empty.elim := by
  simp [models_iff, andDefP]

omit [Nonempty M] [Structure.Eq L6 M] in
theorem eval_maxRHS (a g : M) :
    maxRHS.Eval ![a, g] Empty.elim ↔
      ∃ g₁ g₂, F₁.Eval ![a, g₁] Empty.elim ∧ F₃.Eval ![a, g₂] Empty.elim ∧
        ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂ := by
  simp [maxRHS]

omit [Structure.Eq L6 M] in
theorem models_maxDefF :
    M↓[L6] ⊧ maxDefF ↔ ∀ a g : M, F₅.Eval ![a, g] Empty.elim ↔
      ∃ g₁ g₂, F₁.Eval ![a, g₁] Empty.elim ∧ F₃.Eval ![a, g₂] Empty.elim ∧
        ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂ := by
  simp [models_iff, maxDefF, eval_maxRHS]

end Models

/-- **The conjunction template is a theorem of the template theory.** -/
theorem andTemplate_provable : templTheory 6 ar6 ⊢ andTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [andTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot₁, hrefl₁, htot₃, hrefl₃, hdefP, hdefF⟩
  rw [models_totS] at htot₁ htot₃ ⊢
  rw [models_reflS] at hrefl₁ hrefl₃ ⊢
  rw [models_andDefP] at hdefP
  rw [models_maxDefF] at hdefF
  exact and_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M))
    htot₁ hrefl₁ htot₃ hrefl₃ hdefP hdefF

end LeanProofs.ZFCinPA.LStepAnd
