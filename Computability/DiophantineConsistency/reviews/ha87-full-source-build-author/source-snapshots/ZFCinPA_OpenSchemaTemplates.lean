import ZFCinPA.OpenTemplateClosure
import ZFCinPA.ModelCodedOpenSchemaAxioms

set_option autoImplicit false
noncomputable section

/-!
Actual ZF proofs of translated Separation and globally total Replacement,
including the finite universal closure of the ordinary source parameters.
Internal predicate interpretations retain arbitrary additional free parameters.
-/
namespace LeanProofs.ZFCinPA.OpenSchemaTemplates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.OpenTemplateClosure
open LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms
open scoped LO.FirstOrder.Arithmetic

variable {k : Nat} {arities : Fin k → Nat}
abbrev Lang := setTemplateLanguage k arities
local instance : Language.Mem (Lang (k := k) (arities := arities)) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

def sepBodySource (φ : Semiproposition (Lang (k := k) (arities := arities)) 1) : Proposition (Lang (k := k) (arities := arities)) :=
  “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

/-- The atom `z ∈ y` of the skeleton (level 3; `z = #0`, `y = #1`). -/
def sourceZY : Semiproposition (Lang (k := k) (arities := arities)) 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- The atom `z ∈ x` of the skeleton (level 3; `z = #0`, `x = #2`). -/
def sourceZX : Semiproposition (Lang (k := k) (arities := arities)) 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

/-- The separation body, resolved to its de Bruijn normal form. -/
lemma sepBodySource_eq (φ : Semiproposition (Lang (k := k) (arities := arities)) 1) :
    sepBodySource φ
      = ∀⁰ ∃⁰ ∀⁰ (sourceZY 🡘 (sourceZX ⋏ (φ ⇜ ![(#0 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 3)]))) := by
  simp [sepBodySource, sourceZY, sourceZX, LogicalConnective.iff,
    FirstOrder.Semiformula.Operator.mem_def]

def repBodySource (ψ : Semiproposition (Lang (k := k) (arities := arities)) 2) : Proposition (Lang (k := k) (arities := arities)) :=
  “(∀ x, ∃! y, !ψ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !ψ x y”

/-- The atom `z = y` of the uniqueness clause (level 3; `z = #0`, `y = #1`). -/
def sourceEq : Semiproposition (Lang (k := k) (arities := arities)) 3 :=
  FirstOrder.Semiformula.rel Language.Eq.eq ![#0, #1]

/-- The atom `y ∈ Y` of the collection clause (level 3; `y = #0`, `Y = #1`). -/
def sourceYY : Semiproposition (Lang (k := k) (arities := arities)) 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- The atom `x ∈ X` of the bounded witness (level 4; `x = #0`, `X = #3`). -/
def sourceXX : Semiproposition (Lang (k := k) (arities := arities)) 4 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #3]

/-- The replacement body, resolved to its de Bruijn normal form: `ψ` enters at
three spots, under the substitutions `![#1, #0]`, `![#2, #0]` and `![#0, #1]`. -/
lemma repBodySource_eq (ψ : Semiproposition (Lang (k := k) (arities := arities)) 2) :
    repBodySource ψ
      = (∀⁰ ∃⁰ ((ψ ⇜ ![(#1 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 2), #0])
            ⋏ (∀⁰ ((ψ ⇜ ![(#2 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 3), #0]) 🡒 sourceEq))))
        🡒 (∀⁰ ∃⁰ ∀⁰ (sourceYY
              🡘 (∃⁰ (sourceXX ⋏ (ψ ⇜ ![(#0 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 4), #1]))))) := by
  have h1 : ∀ θ : Semiproposition (Lang (k := k) (arities := arities)) 2,
      (θ ⇜ ((#0 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 2) :> fun _ => #1)) = θ := by
    intro θ
    have hv : ((#0 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 2) :> fun _ => #1) = Semiterm.bvar := by
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl
    rw [hv]
    simp [Rewriting.subst]
  have h2 : (ψ ⇜ ![(#1 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 2), #0])
        ⇜ ((#0 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 3) :> fun _ => #2)
      = ψ ⇜ ![(#2 : SyntacticSemiterm (Lang (k := k) (arities := arities)) 3), #0] := by
    show Rew.subst _ ▹ (Rew.subst _ ▹ ψ) = Rew.subst _ ▹ ψ
    rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
    congr 2
    exact congrArg Rew.subst (by
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl)
  simp [repBodySource, sourceEq, sourceYY, sourceXX, LogicalConnective.iff,
    FirstOrder.Semiformula.Operator.mem_def, FirstOrder.Semiformula.Operator.eq_def,
    FirstOrder.Semiformula.existsUnique, FirstOrder.Semiformula.bexsMem,
    LO.FirstOrder.bexs, h1, h2]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma translate_sepBodySource
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 1) :
    translateFormula Ks (sepBodySource p) = sepBody (translateFormula Ks p) := by
  rw [sepBodySource_eq]
  simp only [translateFormula_neg',translateFormula_neg,translateFormula,translateFormula_subst,
    sepBody,sourceZY,sourceZX,sepAtomZY,sepAtomZX,
    FirstOrder.Semiformula.typed_quote_rel,Semiterm.typed_quote_bvar,
    translateTerm_bvar,LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def,Matrix.comp_vecCons',Matrix.empty_eq]
  all_goals rfl

lemma translate_repBodySource
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    translateFormula Ks (repBodySource p) = repBody (translateFormula Ks p) := by
  rw [repBodySource_eq]
  simp only [translateFormula_neg',translateFormula_neg,translateFormula,translateFormula_subst,
    repBody,sourceEq,sourceYY,sourceXX,repAtomEq,repAtomYY,repAtomXX,
    FirstOrder.Semiformula.typed_quote_rel,Semiterm.typed_quote_bvar,
    translateTerm_bvar,LogicalConnective.iff,FirstOrder.Semiformula.imp_eq,
    Bootstrapping.Semiformula.imp_def,Matrix.comp_vecCons',Matrix.empty_eq]
  all_goals rfl

noncomputable def separationProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 1) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula Ks (Rewriting.emb (sepBodySource p).univCl) := by
  apply closeTemplate Ks _ (sepBodySource p)
  intro b
  rw [translate_sepBodySource]
  exact zfSeparationProof _

noncomputable def replacementProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢!
      translateFormula Ks (Rewriting.emb (repBodySource p).univCl) := by
  apply closeTemplate Ks _ (repBodySource p)
  intro b
  rw [translate_repBodySource]
  exact zfReplacementProof _

/-- A lifted axiom of any definable set theory translates to an internal proof. -/
noncomputable def liftedTheoryProof (T : SetTheory) [T.Δ₁]
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) T) :
    T.internalize V ⊢! translateFormula Ks (Rewriting.emb σ) := by
  apply TProof.byAxm
  rcases h with ⟨τ,hτ,rfl⟩
  rw [translateFormula_lMap_set_emb]
  exact (Bootstrapping.Δ₁Class.mem_iff'' (T := T)).mpr hτ

noncomputable def liftedZFProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory)) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! translateFormula Ks (Rewriting.emb σ) :=
  liftedTheoryProof 𝗭𝗙 Ks σ h

end LeanProofs.ZFCinPA.OpenSchemaTemplates
