import ZFCinPA.LTemplate
import ZFCinPA.LPieces

set_option autoImplicit false
noncomputable section

/-!
# The reflection invariant of the `hSchema` generator

For a unary placeholder `P` (read at an internal environment) and a binary
placeholder `F` (the graph of a function on ordinals), the invariant is the
conjunction of

* `totS F`: `F` is a total function on ordinals with `α ∈ F(α)`;
* `reflS P F`: there is an internal formula code `c` such that at every
  nonzero limit `β` closed under `F`, every environment `t` over an earlier
  stage `L_α` (`α ∈ β`) satisfies `P(t) ↔ (S, R) ⊨ c[t]`, where `S = L_β` and
  `R` is its membership relation. (Environments over earlier stages, rather
  than finitely supported ones, make the quantifier step need only the
  maximum of two ordinals below a limit.)

`models_totS` and `models_reflS` read the two sentences in every model of the
template theory, through the pieces of `LPieces`.
-/

namespace LeanProofs.ZFCinPA.LInvariant

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LPieces

variable {k : ℕ} {arities : Fin k → ℕ}

local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- A set-theoretic semisentence, lifted into the enlarged language. -/
def lift {n : ℕ} (σ : SetTheorySemisentence n) : Semisentence (setTemplateLanguage k arities) n :=
  Semiformula.lMap (setHom k arities) σ

/-- `F` is a total function on ordinals, above its argument. -/
def totS (F : Semisentence (setTemplateLanguage k arities) 2) :
    Sentence (setTemplateLanguage k arities) :=
  “∀ a, !(lift ordP) a → ∃ g, !(lift ordP) g ∧ a ∈ g ∧ !F a g ∧ ∀ h, !F a h → h = g”

/-- At every nonzero limit closed under `F`, `P` is internal satisfaction of one
code over the stage, for environments over earlier stages. -/
def reflS (P : Semisentence (setTemplateLanguage k arities) 1)
    (F : Semisentence (setTemplateLanguage k arities) 2) : Sentence (setTemplateLanguage k arities) :=
  “∃ c, !(lift codeP) c ∧ ∀ b, !(lift limP) b → (∀ a, a ∈ b → ∀ g, !F a g → g ∈ b) →
    ∀ S, !(lift stageP) b S → ∀ R, !(lift memRelP) S R → ∀ a, a ∈ b → ∀ U, !(lift stageP) a U →
      ∀ t, !(lift envP) U t → (!P t ↔ !(lift satP) S R c t)”

/-! ## Semantics in template models -/

section Semantics

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M]
variable [s : Structure (setTemplateLanguage k arities) M]
variable [Structure.Eq (setTemplateLanguage k arities) M]
variable [Structure.Mem (setTemplateLanguage k arities) M]

@[simp] lemma eval_lift {n : ℕ} (σ : SetTheorySemisentence n) (e : Fin n → M) (ε : Empty → M) :
    (lift (k := k) (arities := arities) σ).Eval e ε ↔
      σ.Eval (s := SetTheory.standardStructure M) e ε := LTemplate.eval_set_lMap σ e ε

theorem models_totS (F : Semisentence (setTemplateLanguage k arities) 2) :
    M↓[setTemplateLanguage k arities] ⊧ totS F ↔
      ∀ a : M, Ord (memRel M) a → ∃ g, Ord (memRel M) g ∧ a ∈ g ∧ F.Eval ![a, g] Empty.elim ∧
        ∀ h, F.Eval ![a, h] Empty.elim → h = g := by
  simp [models_iff, totS]

variable [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

theorem models_reflS (P : Semisentence (setTemplateLanguage k arities) 1)
    (F : Semisentence (setTemplateLanguage k arities) 2) :
    M↓[setTemplateLanguage k arities] ⊧ reflS P F ↔
      ∃ c : M, IsFormCodeSem (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) c ∧
        ∀ b : M, IsLim (memRel M) b → (∀ a, a ∈ b → ∀ g, F.Eval ![a, g] Empty.elim → g ∈ b) →
          ∀ S, IsL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
              (ConstructibleInterpretation.power_of_modelsZF (V := M)) b S →
          ∀ R, MemRel (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) S R →
          ∀ a, a ∈ b → ∀ U, IsL (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
              (ConstructibleInterpretation.power_of_modelsZF (V := M)) a U →
          ∀ t, IsEnvOn (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) U t →
            (P.Eval ![t] Empty.elim ↔
              SatIn (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) S R c t) := by
  simp [models_iff, reflS,
    eval_codeP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)),
    eval_stageP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (hP := ConstructibleInterpretation.power_of_modelsZF (V := M)),
    eval_memRelP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)),
    eval_envP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)),
    eval_satP (H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))]

end Semantics

end LeanProofs.ZFCinPA.LInvariant
