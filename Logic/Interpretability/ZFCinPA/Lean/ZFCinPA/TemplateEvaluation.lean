import ZFCinPA.TarskiSources
import ZFCinPA.LocalStepTransfer

/-!
# The evaluation bridge, part one: template structures and their leaves

`ZFCinPA.SetPlaceholderQuotient.complete_underSetPlaceholderCongruence`
reduces a source derivation over `templateZFC 2 levelArities` to a purely
semantic obligation: the source sentence must hold in **every** template
structure `X ⊧* templateZFC 2 ![1, 2]` whose equality symbol denotes genuine
Lean equality.  To use that tool the source formulas of
`ZFCinPA.SuccessorSources` and `ZFCinPA.TarskiSources` have to be
*evaluated* in such an `X` and identified with the abstract closure
semantics of `ZFCinPA.TarskiFieldSemantics` / `ZFCinPA.EnlargedFields`.

This module is the bottom of that bridge — items 1 and 2 of the residue
list in `ZFCinPA.LocalStepTransfer`:

* **Structure setup.**  A template structure carries a membership relation
  `templateMem X` on its `ℒₛₑₜ` summand; `lMap_setHom_eq_standard` proves
  that the `ℒₛₑₜ` reduct of `X` *is* `SetTheory.standardStructure` of that
  relation (this is where `Structure.Eq` is consumed, exactly once), and
  `zfcAxioms_of_template` extracts goal 2's nine-axiom bundle
  `BoundedZFCConsistency.ZFCAxioms (templateMem X)` from
  `X ⊧* templateZFC 2 levelArities` through `ZFCinPA.zfcAxioms_of_models`.
* **Leaf evaluation.**  `eval_liftP` evaluates a lifted fixed `ℒₛₑₜ` leaf
  `liftP (toSet k φ)` as `SetTheory.Sat (templateMem X)` of `φ`, under the
  same environment-correspondence invariant `eval_toSet` uses — packaged
  here once, as the structure `Corr`, with its `cons` step.
* **Placeholder evaluation.**  `eval_srcPProp` reads a placeholder atom as
  the structure's own interpretation of the corresponding relation symbol,
  and `templateNum` / `templateClos` name the two interpretations at the
  arities `levelArities` declares.  `templateLevel` is the *induced
  previous level*
  `LS₁ c e b :≡ ∃ n C, Num n ∧ Clos n C ∧ ⟨c, e, b⟩ ∈ C`
  which every spine reading of `ZFCinPA.SpineEvaluation` is stated over.

Nothing here is assumed anywhere, and nothing here weakens
`StagedSuccessor.ZFCSuccessorImplications`.

## Disciplines

The parameter firewall is irrelevant at this layer — no Gödel constant
occurs in any statement of this module, because the fixed leaves are kept
as `SetTheory.Form`s and only their `Sat` readings are produced.  That is
deliberate: the evaluation side never needs a code, and so never risks
evaluating one.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace TemplateEvaluation

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SuccessorSources

/-! ## The `ℒₛₑₜ` reduct of a template structure -/

section Reduct

variable {X : Type*} [sX : Structure srcL X]

/-- **The membership relation of a template structure**: the interpretation
of the `ℒₛₑₜ` summand's `∈` symbol, in the binary-relation form the
repository's semantic layer consumes. -/
def templateMem (X : Type*) [Structure srcL X] : X → X → Prop :=
  fun a b ↦ Structure.rel (L := srcL) (Sum.inl Language.Set.Rel.mem) ![a, b]

/-- The `SetStructure` — i.e. the `Membership` instance — that
`templateMem` induces.  It is deliberately *not* a global instance: a
template structure is an `srcL`-structure, and turning every such into a
`Membership` would leak into unrelated instance searches. -/
@[reducible] def templateSetStructure (X : Type*) [Structure srcL X] :
    SetStructure X :=
  ⟨fun y x ↦ templateMem X x y⟩

/-- The orientation check: `ZFCinPA.memRel` of the induced set structure is
`templateMem`, on the nose. -/
theorem memRel_templateSetStructure :
    @memRel X (templateSetStructure X) = templateMem X := rfl

/-- **The `ℒₛₑₜ` reduct is the standard structure of `templateMem`.**  This
is the single place where genuine equality is consumed: the reduct's `=`
symbol denotes Lean equality precisely because `X` carries
`Structure.Eq srcL X`, and the `∈` symbol denotes `templateMem` by
definition.  Foundation's `standardStructure` is then forced. -/
theorem lMap_setHom_eq_standard [Structure.Eq srcL X] :
    sX.lMap (setHom 2 levelArities) =
      @SetTheory.standardStructure X (templateSetStructure X) := by
  refine Structure.ext (funext₃ fun _ f _ ↦ f.elim) (funext₃ fun _ r v ↦ ?_)
  cases r with
  | eq =>
      have h : Structure.rel (L := srcL) (Language.Eq.eq) v ↔ v 0 = v 1 :=
        Structure.eq_lang (L := srcL) (M := X) (v := v)
      exact propext h
  | mem =>
      show Structure.rel (L := srcL) (Sum.inl Language.Set.Rel.mem) v =
        (templateMem X (v 0) (v 1))
      show _ = Structure.rel (L := srcL) (Sum.inl Language.Set.Rel.mem)
        ![v 0, v 1]
      rw [← Matrix.fun_eq_vec_two (v := v)]

end Reduct

/-! ## The nine-axiom bundle -/

section Bundle

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **The `ℒₛₑₜ` reduct models `𝗭𝗙𝗖`.**  Every axiom of
`templateZFC 2 levelArities` is a lifted `𝗭𝗙𝗖` axiom, so this is
`Semiformula.models_lMap` followed by the reduct identification. -/
theorem models_zfc_of_template
    [hZFC : X↓[srcL] ⊧* templateZFC 2 levelArities] :
    letI : SetStructure X := templateSetStructure X
    X↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖 : SetTheory) := by
  letI : SetStructure X := templateSetStructure X
  constructor
  intro σ hσ
  have h : X↓[srcL] ⊧ Semiformula.lMap (setHom 2 levelArities) σ :=
    hZFC.models _ ⟨σ, hσ, rfl⟩
  have h2 := Semiformula.models_lMap.mp h
  rwa [lMap_setHom_eq_standard] at h2

/-- **Bundle extraction for template structures.**  Goal 2's nine-axiom
semantic bundle over the induced membership relation, from
`ZFCinPA.zfcAxioms_of_models`. -/
theorem zfcAxioms_of_template
    [X↓[srcL] ⊧* templateZFC 2 levelArities] :
    BoundedZFCConsistency.ZFCAxioms (templateMem X) := by
  letI : SetStructure X := templateSetStructure X
  haveI : X↓[ℒₛₑₜ] ⊧* (𝗭𝗙𝗖 : SetTheory) := models_zfc_of_template
  exact zfcAxioms_of_models

/-- The six-clause `ZFAxioms` bundle, which is what the abstract closure
semantics is stated over. -/
theorem zfAxioms_of_template
    [X↓[srcL] ⊧* templateZFC 2 levelArities] :
    SetTheory.ZFAxioms (templateMem X) :=
  (zfcAxioms_of_template (X := X)).toZFAxioms

end Bundle

/-! ## The environment-correspondence invariant

`ZFCinPA.eval_toSet` relates Foundation's two-part valuation `(b, f)` at
depth `k` to a single repository environment `e`.  Every spine lemma below
carries the same invariant, so it is named once here together with its
step through a binder. -/

section Corr

variable {X : Type*}

/-- The Foundation valuation `(b, f)` at depth `k` reads the repository
environment `e`: the `k` bound slots are `e 0, …, e (k-1)` and the free
slots continue at `e k`. -/
structure Corr {k : ℕ} (b : Fin k → X) (f e : ℕ → X) : Prop where
  /-- The bound slots. -/
  bvar : ∀ i : Fin k, b i = e i.val
  /-- The free slots. -/
  fvar : ∀ j, f j = e (k + j)

/-- At depth zero every free assignment corresponds to itself. -/
theorem Corr.zero (f : ℕ → X) : Corr (k := 0) ![] f f :=
  ⟨fun i ↦ i.elim0, fun j ↦ by rw [Nat.zero_add]⟩

/-- **The invariant steps through a binder.**  Prepending `x` on the
Foundation side matches `SetTheory.scons x` on the repository side. -/
theorem Corr.cons {k : ℕ} {b : Fin k → X} {f e : ℕ → X} (h : Corr b f e)
    (x : X) : Corr (x :> b) f (SetTheory.scons x e) := by
  refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · refine Fin.cases ?_ (fun i' ↦ ?_) i
    · simp [SetTheory.scons]
    · simpa [SetTheory.scons] using h.bvar i'
  · have h2 : k + 1 + j = (k + j) + 1 := by omega
    rw [h2]
    simpa [SetTheory.scons] using h.fvar j

end Corr

/-! ## Leaf evaluation -/

section Leaves

variable {X : Type*} [Nonempty X] [sX : Structure srcL X] [Structure.Eq srcL X]

/-- **A lifted fixed `ℒₛₑₜ` leaf evaluates to its repository reading.**
This is `ZFCinPA.eval_toSet` composed with `Semiformula.eval_lMap` and the
reduct identification. -/
theorem eval_liftP {k : ℕ} {b : Fin k → X} {f e : ℕ → X} (h : Corr b f e)
    (φ : SetTheory.Form) :
    Semiformula.Eval (s := sX) b f (liftP (toSet k φ)) ↔
      SetTheory.Sat (templateMem X) e φ := by
  letI : SetStructure X := templateSetStructure X
  show Semiformula.Eval (s := sX) b f
    (Semiformula.lMap (setHom 2 levelArities) (toSet k φ)) ↔ _
  rw [Semiformula.eval_lMap, lMap_setHom_eq_standard]
  exact eval_toSet φ k b f e h.bvar h.fvar

end Leaves

/-! ## Placeholder evaluation -/

section Placeholders

variable {X : Type*} [sX : Structure srcL X]

/-- **The interpretation of the `i`-th placeholder relation** in a template
structure. -/
def templateRel (X : Type*) [Structure srcL X] (i : Fin 2)
    (v : Fin (levelArities i) → X) : Prop :=
  Structure.rel (L := srcL) (placeholderRel i) v

/-- **A placeholder atom evaluates to the structure's own relation** at the
values of its argument terms. -/
theorem eval_srcPProp {n : ℕ} (i : Fin 2)
    (ts : Fin (levelArities i) → SyntacticSemiterm srcL n)
    (b : Fin n → X) (f : ℕ → X) :
    Semiformula.Eval (s := sX) b f (srcPProp i ts) ↔
      templateRel X i (fun j ↦ Semiterm.val b f (ts j)) := by
  rw [srcPProp, Semiformula.eval_rel]
  rfl

/-- The unary placeholder: "is a numeral index". -/
def templateNum (X : Type*) [Structure srcL X] (n : X) : Prop :=
  templateRel X 0 ![n]

/-- The binary placeholder: "`C` is the closure certificate at index `n`". -/
def templateClos (X : Type*) [Structure srcL X] (n C : X) : Prop :=
  templateRel X 1 ![n, C]

/-- The numeral-chain placeholder at the identity argument list. -/
theorem eval_srcNumAt {n : ℕ} (hn : 1 ≤ n) (b : Fin n → X) (f : ℕ → X) :
    Semiformula.Eval (s := sX) b f (srcNumAt hn) ↔
      templateNum X (b ⟨0, by omega⟩) := by
  rw [srcNumAt, srcPlaceholder, eval_srcPProp, templateNum]
  refine iff_of_eq (congrArg (templateRel X 0) (funext fun j ↦ ?_))
  match j with
  | ⟨0, _⟩ => rfl

/-- The closure-kernel placeholder at the identity argument list. -/
theorem eval_srcClsAt {n : ℕ} (hn : 2 ≤ n) (b : Fin n → X) (f : ℕ → X) :
    Semiformula.Eval (s := sX) b f (srcClsAt hn) ↔
      templateClos X (b ⟨0, by omega⟩) (b ⟨1, by omega⟩) := by
  rw [srcClsAt, srcPlaceholder, eval_srcPProp, templateClos]
  refine iff_of_eq (congrArg (templateRel X 1) (funext fun j ↦ ?_))
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

end Placeholders

/-! ## The induced previous level

The two placeholders are opaque, so the only level relation a template
structure supplies is the one the source spine reads off them.  This is the
relation `L` that every statement of `ZFCinPA.EnlargedFields` and
`ZFCinPA.LocalStepTransfer` is universally quantified over. -/

section Level

variable {X : Type*} [Structure srcL X]

open BoundedZFCConsistency
open SetTheory (ZFAxioms)

/-- **The previous level induced by the two placeholders**, exactly as
`ZFCinPA.LocalStepTransfer`'s residue item 3 records it:
`LS₁ c e b :≡ ∃ n C, Num n ∧ Clos n C ∧ ⟨c, e, b⟩ ∈ C`. -/
def templateLevel (X : Type*) [Structure srcL X]
    (H : ZFAxioms (templateMem X)) (c e b : X) : Prop :=
  ∃ n C, templateNum X n ∧ templateClos X n C ∧
    templateMem X (satTriple H c e b) C

end Level

end TemplateEvaluation
end ZFCinPA
end LeanProofs
