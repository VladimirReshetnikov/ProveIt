import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding

/-!
# Specializing standard proof templates at model-coded formulas

The ordinary quotation operation turns a standard `Derivation2` into an
internal derivation by replacing every standard term and formula with its
quotation.  A uniform partial-truth construction needs a slightly more
general operation: one relation symbol in a fixed, standard proof template
will be replaced by a formula whose code is an arbitrary element of a model
of arithmetic.  In particular, that formula need not decode to a standard
Lean syntax tree.

This file isolates the purely logical part of that operation.  A
`TypedTemplateTranslation` supplies typed translations of standard terms and
formulas and the five equations used by the proof rules.  The compiler below
then follows a standard `Derivation2` node by node and emits the corresponding
`TDerivation`.  Every emitted proof code is therefore checked by Foundation's
represented derivation predicate; no semantic soundness or standardness
assumption is used.

The interface is intentionally more general than a single placeholder
language.  Later modules may instantiate it with several predicate symbols
or with fixed arithmetic syntax plus one model-coded truth predicate.
-/

namespace LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

variable {L₁ L₂ : Language}
variable [L₁.DecidableEq]
variable [L₂.Encodable] [L₂.LORDefinable]

/-- The equations needed to specialize a standard one-sided derivation.

`formula` translates standard formulas to typed formulas in the arithmetic
model.  The operation can therefore insert genuinely nonstandard syntax.
The equations are exactly those inspected by `Derivation2`; keeping them as
fields makes the proof compiler independent of the concrete placeholder
language used later. -/
structure TypedTemplateTranslation (V : Type*) (L₁ L₂ : Language)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
    [L₂.Encodable] [L₂.LORDefinable] where
  term : {n : ℕ} → SyntacticSemiterm L₁ n →
    Bootstrapping.Semiterm V L₂ n
  formula : {n : ℕ} → Semiproposition L₁ n →
    Bootstrapping.Semiformula V L₂ n
  formula_neg : ∀ {n} (p : Semiproposition L₁ n),
    formula (∼p) = ∼formula p
  formula_and : ∀ {n} (p q : Semiproposition L₁ n),
    formula (p ⋏ q) = formula p ⋏ formula q
  formula_or : ∀ {n} (p q : Semiproposition L₁ n),
    formula (p ⋎ q) = formula p ⋎ formula q
  formula_verum : ∀ {n},
    formula (⊤ : Semiproposition L₁ n) = ⊤
  formula_all : ∀ {n} (p : Semiproposition L₁ (n + 1)),
    formula (∀⁰ p) = ∀⁰ formula p
  formula_exs : ∀ {n} (p : Semiproposition L₁ (n + 1)),
    formula (∃⁰ p) = ∃⁰ formula p
  formula_shift : ∀ {n} (p : Semiproposition L₁ n),
    formula (Rewriting.shift p) = (formula p).shift
  formula_free : ∀ (p : Semiproposition L₁ 1),
    formula (Rewriting.free p) = (formula p).free
  formula_subst₁ : ∀ (p : Semiproposition L₁ 1)
      (t : SyntacticTerm L₁),
    formula (p/[t]) = (formula p).subst ![term t]

namespace TypedTemplateTranslation

variable (tr : TypedTemplateTranslation V L₁ L₂)

/-- Translate a finite standard sequent into an HFS-coded typed sequent.

We fold over a list instead of choosing a code for a mapped finite set.  The
membership theorem below makes the construction's order irrelevant and also
handles translations which identify two source formulas. -/
noncomputable def translateList :
    List (Proposition L₁) → Bootstrapping.Sequent V L₂
  | [] => ∅
  | p :: Γ => insert (tr.formula p) (translateList Γ)

noncomputable def translateSequent
    (Γ : Finset (Proposition L₁)) : Bootstrapping.Sequent V L₂ :=
  translateList (tr := tr) Γ.toList

lemma mem_translateList_iff {q : V}
    {Γ : List (Proposition L₁)} :
    q ∈ (tr.translateList Γ).val ↔
      ∃ p ∈ Γ, (tr.formula p).val = q := by
  induction Γ with
  | nil => simp [translateList]
  | cons p Γ ih =>
      simp only [translateList, Bootstrapping.Sequent.val_insert,
        mem_bitInsert_iff, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨r, hr, htr⟩)
        · exact ⟨p, Or.inl rfl, rfl⟩
        · exact ⟨r, Or.inr hr, htr⟩
      · rintro ⟨r, rfl | hr, htr⟩
        · exact Or.inl htr.symm
        · exact Or.inr ⟨r, hr, htr⟩

lemma mem_translateSequent_iff {q : V}
    {Γ : Finset (Proposition L₁)} :
    q ∈ (tr.translateSequent Γ).val ↔
      ∃ p ∈ Γ, (tr.formula p).val = q := by
  simp only [translateSequent, mem_translateList_iff,
    Finset.mem_toList]

lemma formula_mem_translateSequent {p : Proposition L₁}
    {Γ : Finset (Proposition L₁)} (hp : p ∈ Γ) :
    tr.formula p ∈ tr.translateSequent Γ := by
  exact (mem_translateSequent_iff (tr := tr)).mpr ⟨p, hp, rfl⟩

lemma translateSequent_insert (p : Proposition L₁)
    (Γ : Finset (Proposition L₁)) :
    tr.translateSequent (insert p Γ) =
      insert (tr.formula p) (tr.translateSequent Γ) := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  simp only [mem_translateSequent_iff,
    Bootstrapping.Sequent.val_insert, mem_bitInsert_iff,
    Finset.mem_insert]
  constructor
  · rintro ⟨r, rfl | hr, htr⟩
    · exact Or.inl htr.symm
    · exact Or.inr ⟨r, hr, htr⟩
  · rintro (rfl | ⟨r, hr, htr⟩)
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨r, Or.inr hr, htr⟩

lemma translateSequent_singleton (p : Proposition L₁) :
    tr.translateSequent {p} =
      ({tr.formula p} : Bootstrapping.Sequent V L₂) := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  simp only [mem_translateSequent_iff,
    Bootstrapping.Sequent.val_singleton, mem_singleton_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, rfl, htr⟩
    exact htr.symm
  · rintro rfl
    exact ⟨p, rfl, rfl⟩

lemma translateSequent_mono {Γ Δ : Finset (Proposition L₁)}
    (h : Γ ⊆ Δ) :
    tr.translateSequent Γ ⊆ tr.translateSequent Δ := by
  intro q hq
  rcases (mem_translateSequent_iff (tr := tr)).mp hq with ⟨p, hp, rfl⟩
  exact formula_mem_translateSequent tr (h hp)

lemma translateSequent_image_shift (Γ : Finset (Proposition L₁)) :
    tr.translateSequent (Γ.image Rewriting.shift) =
      (tr.translateSequent Γ).shift := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  rw [mem_translateSequent_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨r, hr, rfl⟩
    rw [tr.formula_shift]
    exact Bootstrapping.mem_setShift_iff.mpr
      ⟨(tr.formula r).val,
        (formula_mem_translateSequent tr hr), rfl⟩
  · intro hq
    rcases Bootstrapping.mem_setShift_iff.mp hq with ⟨r, hr, hqr⟩
    rcases (mem_translateSequent_iff (tr := tr)).mp hr with ⟨p, hp, rfl⟩
    refine ⟨Rewriting.shift p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [tr.formula_shift]
    exact hqr.symm

end TypedTemplateTranslation

/-- A template translation whose source axioms are mapped to axioms of the
target internal theory. -/
structure TypedTheoryTemplateTranslation
    (T₁ : Theory L₁) (T₂ : InternalTheory V L₂)
    extends TypedTemplateTranslation V L₁ L₂ where
  axiom_mem : ∀ (σ : Sentence L₁), σ ∈ T₁ →
    formula (Rewriting.emb σ : Proposition L₁) ∈' T₂.theory

namespace TypedTheoryTemplateTranslation

variable {T₁ : Theory L₁} {T₂ : InternalTheory V L₂}
variable (tr : TypedTheoryTemplateTranslation T₁ T₂)

/-- Compile a standard derivation tree into a represented derivation tree
after translating every formula.

This is the model-coded analogue of `Derivation2.typedQuote`.  Recursion is
over the fixed, standard proof template; the inserted target formulas may
nevertheless have nonstandard codes. -/
noncomputable def compileDerivation {Γ : Finset (Proposition L₁)} :
    T₁ ⟹₂ Γ → T₂ ⊢!ᵈᵉʳ tr.toTypedTemplateTranslation.translateSequent Γ
  | .closed Δ p hp hn =>
      TDerivation.em (tr.formula p)
        (tr.toTypedTemplateTranslation.formula_mem_translateSequent hp)
        (by
          rw [← tr.formula_neg]
          exact tr.toTypedTemplateTranslation.formula_mem_translateSequent hn)
  | .axm σ hT hΓ =>
      TDerivation.byAxm (tr.formula (Rewriting.emb σ : Proposition L₁))
        (tr.axiom_mem σ hT)
        (tr.toTypedTemplateTranslation.formula_mem_translateSequent hΓ)
  | .verum h =>
      TDerivation.verum (by
        rw [← tr.formula_verum]
        exact tr.toTypedTemplateTranslation.formula_mem_translateSequent h)
  | .and (φ := p) (ψ := q) h dp dq =>
      TDerivation.and'
        (by
          rw [← tr.formula_and]
          exact tr.toTypedTemplateTranslation.formula_mem_translateSequent h)
        ((compileDerivation dp).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert]))
        ((compileDerivation dq).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert]))
  | .or (φ := p) (ψ := q) h d =>
      TDerivation.or'
        (by
          rw [← tr.formula_or]
          exact tr.toTypedTemplateTranslation.formula_mem_translateSequent h)
        ((compileDerivation d).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert,
            tr.toTypedTemplateTranslation.translateSequent_insert]))
  | .all (φ := p) h d =>
      TDerivation.all'
        (by
          rw [← tr.formula_all]
          exact tr.toTypedTemplateTranslation.formula_mem_translateSequent h)
        ((compileDerivation d).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert,
            tr.formula_free,
            tr.toTypedTemplateTranslation.translateSequent_image_shift]))
  | .exs (φ := p) h t d =>
      TDerivation.exs'
        (by
          rw [← tr.formula_exs]
          exact tr.toTypedTemplateTranslation.formula_mem_translateSequent h)
        (tr.term t)
        ((compileDerivation d).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert,
            tr.formula_subst₁]))
  | .wk d h =>
      TDerivation.wk (compileDerivation d)
        (tr.toTypedTemplateTranslation.translateSequent_mono h)
  | .shift d =>
      (TDerivation.shift (compileDerivation d)).cast (by
        rw [tr.toTypedTemplateTranslation.translateSequent_image_shift])
  | .cut (φ := p) d dn =>
      TDerivation.cut (φ := tr.formula p)
        ((compileDerivation d).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert]))
        ((compileDerivation dn).cast (by
          rw [tr.toTypedTemplateTranslation.translateSequent_insert,
            tr.formula_neg]))

/-- Specialize a standard proof object and return a typed proof of its
translated conclusion. -/
noncomputable def compileProof {σ : Sentence L₁}
    (d : T₁ ⊢! σ) : T₂ ⊢! tr.formula (Rewriting.emb σ) := by
  let d₂ : T₁ ⊢!₂! (Rewriting.emb σ : Proposition L₁) := d.toProof2
  apply (compileDerivation (tr := tr) d₂).cast
  simpa [Bootstrapping.Sequent.insert_empty_eq_singleton] using
    tr.toTypedTemplateTranslation.translateSequent_singleton
      (Rewriting.emb σ : Proposition L₁)

/-- The compiled proof's carrier is accepted by the represented target
proof predicate. -/
lemma compileProof_isProof {σ : Sentence L₁}
    (d : T₁ ⊢! σ) :
    Proof T₂.theory (compileProof (tr := tr) d).val
      (tr.formula (Rewriting.emb σ)).val := by
  simpa [Proof] using (compileProof (tr := tr) d).derivationOf

end TypedTheoryTemplateTranslation

end LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler
