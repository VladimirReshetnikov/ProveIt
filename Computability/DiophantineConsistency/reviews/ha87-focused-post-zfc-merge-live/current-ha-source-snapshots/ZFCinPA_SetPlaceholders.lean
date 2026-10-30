import ZFCinPA.ZFDelta1
import BoundedPAConsistency.TypedTemplateProofCompiler

/-!
# Indexed placeholder relations over `ℒₛₑₜ` and their model-coded translation

`ZFCinPA.SeparationKernel` compiles fixed source proofs over `ℒₛₑₜ` enlarged
by *one* unary placeholder relation into internal `𝗭𝗙𝗖` proofs about a
model-coded formula.  The staged certificate compiler needs the general form:
a tuple of placeholder relations with specified arities — one main predicate
(the current truth predicate, arity `3` in the canonical slot assignment)
together with parameter predicates.  This module supplies that apparatus
once, for an arbitrary arity tuple `arities : Fin k → ℕ`.

The arithmetic project (`BoundedPAConsistency.ModelCodedPredicateParameters`)
carried model parameters as *nullary function symbols*, translated to typed
numerals.  That mechanism cannot transfer: `ℒₛₑₜ` has no function symbols and
no numerals.  Parameters here are therefore additional placeholder
*relations*, translated — like the main predicate — to shift-fixed
model-coded `ℒₛₑₜ` formulas.  A unary parameter placeholder interpreted by a
shift-fixed formula with one free slot plays exactly the role the arithmetic
side gave to a named constant.

Contents:

* `multiPlaceholderLanguage k arities` — `k` relation symbols, the `i`-th of
  arity `arities i`, and no function symbols;
* `setTemplateLanguage k arities := Language.add ℒₛₑₜ (multiPlaceholderLanguage k arities)`
  and the inclusion `setHom`;
* `translateTerm` / `translateFormula Ks` — specialization of every
  placeholder atom by substitution into the chosen model-coded formulas
  `Ks i : Bootstrapping.Semiformula V ℒₛₑₜ (arities i)`, commuting with
  negation, shift, substitution, and `free`;
* `setTemplateTranslation` — the `TypedTemplateTranslation` record consumed
  by the generic typed template proof compiler;
* `templateZFC k arities := Theory.lMap (setHom k arities) 𝗭𝗙𝗖`, the theory
  translation `templateZFCTranslation`, and `compileSetTemplate`, which turns
  an ordinary Lean proof over the lifted `𝗭𝗙𝗖` into an internal
  `𝗭𝗙𝗖.internalize V` proof at the model-coded interpretation — nonstandard
  formula codes included.

Everything here keeps the leaf formulas `Ks i` opaque: no concrete Gödel
code is ever produced or normalized (the parameter-firewall discipline of
`ZFCinPA.LevelCodeTower`).
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SetPlaceholders

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler

/-! ## The indexed placeholder language

A relation symbol of arity `m` is an index `i : Fin k` whose declared arity
is `m`.  Encoding the symbols as a subtype of `Fin k` (rather than an
indexed inductive) makes decidable equality and encodability free of
dependent-index case analysis. -/

/-- `k` placeholder relation symbols, the `i`-th inhabiting exactly the
arity `arities i`; no function symbols. -/
@[reducible] def multiPlaceholderLanguage (k : ℕ) (arities : Fin k → ℕ) :
    Language where
  Func := fun _ ↦ PEmpty
  Rel := fun m ↦ {i : Fin k // arities i = m}

instance (k : ℕ) (arities : Fin k → ℕ) (m : ℕ) :
    DecidableEq ((multiPlaceholderLanguage k arities).Func m) :=
  fun a _ ↦ nomatch a

instance (k : ℕ) (arities : Fin k → ℕ) (m : ℕ) :
    Encodable ((multiPlaceholderLanguage k arities).Func m) :=
  IsEmpty.toEncodable

instance (k : ℕ) (arities : Fin k → ℕ) (m : ℕ) :
    DecidableEq ((multiPlaceholderLanguage k arities).Rel m) :=
  inferInstanceAs (DecidableEq {i : Fin k // arities i = m})

instance (k : ℕ) (arities : Fin k → ℕ) (m : ℕ) :
    Encodable ((multiPlaceholderLanguage k arities).Rel m) :=
  inferInstanceAs (Encodable {i : Fin k // arities i = m})

instance (k : ℕ) (arities : Fin k → ℕ) :
    (multiPlaceholderLanguage k arities).DecidableEq where
  func := fun _ ↦ inferInstance
  rel := fun _ ↦ inferInstance

/-- `ℒₛₑₜ` together with the `k` placeholder relations. -/
@[reducible] def setTemplateLanguage (k : ℕ) (arities : Fin k → ℕ) :
    Language :=
  Language.add ℒₛₑₜ (multiPlaceholderLanguage k arities)

instance (k : ℕ) (arities : Fin k → ℕ) :
    (setTemplateLanguage k arities).DecidableEq where
  func := fun m ↦ by
    change DecidableEq
      ((ℒₛₑₜ).Func m ⊕ (multiPlaceholderLanguage k arities).Func m)
    infer_instance
  rel := fun m ↦ by
    change DecidableEq
      ((ℒₛₑₜ).Rel m ⊕ (multiPlaceholderLanguage k arities).Rel m)
    infer_instance

/-- The `i`-th placeholder as a relation symbol of the template language. -/
def placeholderRel {k : ℕ} {arities : Fin k → ℕ} (i : Fin k) :
    (setTemplateLanguage k arities).Rel (arities i) :=
  Sum.inr ⟨i, rfl⟩

/-- The inclusion of `ℒₛₑₜ` into the placeholder-enlarged language. -/
noncomputable def setHom (k : ℕ) (arities : Fin k → ℕ) :
    ℒₛₑₜ →ᵥ setTemplateLanguage k arities :=
  Language.Hom.add₁ ℒₛₑₜ (multiPlaceholderLanguage k arities)

@[simp] theorem setHom_rel {k : ℕ} {arities : Fin k → ℕ} {m : ℕ}
    (r : (ℒₛₑₜ).Rel m) : (setHom k arities).rel r = Sum.inl r := rfl

/-- Convenience arity tuple: one main predicate of arity `a` followed by
`p` unary parameter placeholders.  Index `0` is the main predicate. -/
@[reducible] def mainWithUnaryParams (a p : ℕ) : Fin (p + 1) → ℕ :=
  a :> fun _ ↦ 1

/-! ## Specialization into typed `ℒₛₑₜ` syntax -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {arities : Fin k → ℕ}

section translation

variable {n m : ℕ}

/-- Interpret source terms as typed terms in the ambient model.  Neither
summand of the template language has function symbols, so a term is a
variable; free-variable indices are embedded as elements of the model. -/
noncomputable def translateTerm :
    SyntacticSemiterm (setTemplateLanguage k arities) n →
      Bootstrapping.Semiterm V ℒₛₑₜ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func (Sum.inl f) _ => f.elim
  | .func (Sum.inr f) _ => f.elim

/-- Replace each placeholder atom by substitution into the corresponding
model-coded formula and retain the set-theoretic and logical constructors
literally.  A placeholder symbol `r` at ambient arity `m` carries the proof
`r.2 : arities r.1 = m`, so its argument vector is reindexed by `Fin.cast`. -/
noncomputable def translateFormula
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) :
    {n : ℕ} → Semiproposition (setTemplateLanguage k arities) n →
      Bootstrapping.Semiformula V ℒₛₑₜ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, .rel (Sum.inl r) v => .rel r fun i ↦ translateTerm (v i)
  | _, .rel (Sum.inr r) v =>
      (Ks r.1).subst fun j ↦ translateTerm (v (Fin.cast r.2 j))
  | _, .nrel (Sum.inl r) v => .nrel r fun i ↦ translateTerm (v i)
  | _, .nrel (Sum.inr r) v =>
      ∼((Ks r.1).subst fun j ↦ translateTerm (v (Fin.cast r.2 j)))
  | _, p ⋏ q => translateFormula Ks p ⋏ translateFormula Ks q
  | _, p ⋎ q => translateFormula Ks p ⋎ translateFormula Ks q
  | _, ∀⁰ p => ∀⁰ translateFormula Ks p
  | _, ∃⁰ p => ∃⁰ translateFormula Ks p

/-! ### Compatibility with rewriting -/

@[simp] theorem translateTerm_shift
    (t : SyntacticSemiterm (setTemplateLanguage k arities) n) :
    translateTerm (V := V) (Rew.shift t) =
      (translateTerm (V := V) t).shift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateTerm_bShift
    (t : SyntacticSemiterm (setTemplateLanguage k arities) n) :
    translateTerm (V := V) (Rew.bShift t) =
      (translateTerm (V := V) t).bShift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateTerm_subst
    (w : Fin n → SyntacticSemiterm (setTemplateLanguage k arities) m)
    (t : SyntacticSemiterm (setTemplateLanguage k arities) n) :
    translateTerm (V := V) (Rew.subst w t) =
      (translateTerm (V := V) t).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateFormula_neg
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (∼p) = ∼translateFormula Ks p := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | hrel r v =>
      rcases r with r | r <;> simp [translateFormula]
  | hnrel r v =>
      rcases r with r | r <;> simp [translateFormula]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_shift
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i)
    (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (Rewriting.shift p) =
      (translateFormula Ks p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n m r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · simp [translateFormula, Bootstrapping.Semiformula.shift_substs,
          hKs r.1, Matrix.map, Function.comp_def]
  | @hnrel n m r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · simp [translateFormula, Bootstrapping.Semiformula.shift_substs,
          hKs r.1, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_subst
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (w : Fin n → SyntacticSemiterm (setTemplateLanguage k arities) m)
    (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (Rew.subst w ▹ p) =
      (translateFormula Ks p).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction p using FirstOrder.Semiformula.rec' generalizing m with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n m r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · simp [translateFormula, Bootstrapping.Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | @hnrel n m r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · simp [translateFormula, Bootstrapping.Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp =>
      simp only [Rewriting.app_all, translateFormula,
        Bootstrapping.Semiformula.substs_all]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [Bootstrapping.SemitermVec.q, translateTerm_bShift, Matrix.map]
  | hexs p hp =>
      simp only [Rewriting.app_exs, translateFormula,
        Bootstrapping.Semiformula.substs_ex]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [Bootstrapping.SemitermVec.q, translateTerm_bShift, Matrix.map]

/-- The special `free` operation used by the universal proof rule also
commutes with placeholder specialization. -/
@[simp] theorem translateFormula_free
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i)
    (p : Semiproposition (setTemplateLanguage k arities) 1) :
    translateFormula Ks (Rewriting.free p) =
      (translateFormula Ks p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst, translateFormula_shift Ks hKs]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-! ### The compiler translation record -/

/-- The concrete syntax translation consumed by the generic typed template
proof compiler. -/
noncomputable def setTemplateTranslation
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) :
    TypedTemplateTranslation V (setTemplateLanguage k arities) ℒₛₑₜ where
  term := translateTerm
  formula := translateFormula Ks
  formula_neg := translateFormula_neg Ks
  formula_and := fun _ _ ↦ rfl
  formula_or := fun _ _ ↦ rfl
  formula_verum := rfl
  formula_all := fun _ ↦ rfl
  formula_exs := fun _ ↦ rfl
  formula_shift := translateFormula_shift Ks hKs
  formula_free := translateFormula_free Ks hKs
  formula_subst₁ := fun p t ↦ by
    exact translateFormula_subst (V := V) Ks ![t] p

/-! ### Lifted `ℒₛₑₜ` material specializes to its quotation -/

/-- On the `ℒₛₑₜ` sublanguage, term specialization is ordinary typed
quotation. -/
@[simp] theorem translateTerm_lMap_set (t : SyntacticSemiterm ℒₛₑₜ n) :
    translateTerm (V := V) (t.lMap (setHom k arities)) =
      (⌜t⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih => exact f.elim

/-- On formulas which do not mention a placeholder, specialization is
ordinary typed quotation. -/
@[simp] theorem translateFormula_lMap_set
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : SetTheorySemiproposition n) :
    translateFormula Ks (p.lMap (setHom k arities)) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      simp only [FirstOrder.Semiformula.lMap_rel, setHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_set]
  | hnrel r v =>
      simp only [FirstOrder.Semiformula.lMap_nrel, setHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_set]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

/-- Sentence-level form of `translateFormula_lMap_set`: a lifted `ℒₛₑₜ`
sentence specializes to its typed quotation. -/
@[simp] theorem translateFormula_lMap_set_emb
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (σ : SetTheorySentence) :
    translateFormula Ks
        (Rewriting.emb (σ.lMap (setHom k arities)) :
          Proposition (setTemplateLanguage k arities)) =
      (⌜σ⌝ : Bootstrapping.Formula V ℒₛₑₜ) := by
  rw [← FirstOrder.Semiformula.lMap_emb, Sentence.typed_quote_def]
  exact translateFormula_lMap_set Ks (Rewriting.emb σ : SetTheoryProposition)

end translation

/-! ## Source atoms and their specialized shapes

The source atoms mirror `SeparationKernel.srcMem`/`srcP`; the equality atom
is added because congruence sentences mention it. -/

section shapes

variable {n : ℕ}

/-- The membership atom of the source language. -/
def srcMem (t u : ClosedSemiterm (setTemplateLanguage k arities) n) :
    Semisentence (setTemplateLanguage k arities) n :=
  .rel (Sum.inl Language.Set.Rel.mem) ![t, u]

/-- The equality atom of the source language. -/
def srcEq (t u : ClosedSemiterm (setTemplateLanguage k arities) n) :
    Semisentence (setTemplateLanguage k arities) n :=
  .rel (Sum.inl Language.Set.Rel.eq) ![t, u]

/-- The `i`-th placeholder atom of the source language. -/
def srcP (i : Fin k)
    (ts : Fin (arities i) → ClosedSemiterm (setTemplateLanguage k arities) n) :
    Semisentence (setTemplateLanguage k arities) n :=
  .rel (placeholderRel i) ts

/-- Lift a fixed `ℒₛₑₜ` formula into the source language. -/
noncomputable def liftSet (φ : SetTheorySemisentence n) :
    Semisentence (setTemplateLanguage k arities) n :=
  φ.lMap (setHom k arities)

/-- `translateFormula_neg`, restated on the primitive negation so that it
also fires after `imp_eq`-style unfolding. -/
@[simp] theorem translateFormula_neg'
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (FirstOrder.Semiformula.neg p) =
      ∼translateFormula Ks p :=
  translateFormula_neg Ks p

/-- Specialization commutes with implication (which is negation-normal-form
sugar on both sides). -/
@[simp] theorem translateFormula_imp
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p q : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (p 🡒 q) =
      translateFormula Ks p 🡒 translateFormula Ks q := by
  rw [FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def]
  simp [translateFormula]

/-- Specialization commutes with bi-implication. -/
@[simp] theorem translateFormula_iff
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (p q : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (p 🡘 q) =
      translateFormula Ks p 🡘 translateFormula Ks q := by
  rw [show p 🡘 q = (p 🡒 q) ⋏ (q 🡒 p) from rfl,
    show translateFormula Ks p 🡘 translateFormula Ks q
      = (translateFormula Ks p 🡒 translateFormula Ks q)
        ⋏ (translateFormula Ks q 🡒 translateFormula Ks p) from rfl]
  simp [translateFormula, Bootstrapping.Semiformula.imp_def]

/-- Source bound variables specialize to typed bound variables. -/
@[simp] theorem translateTerm_bvar (i : Fin n) :
    translateTerm (V := V)
        (#i : SyntacticSemiterm (setTemplateLanguage k arities) n) =
      .bvar i := rfl

/-- The lifted `ℒₛₑₜ` pieces of a source sentence specialize to their typed
quotations, at every arity. -/
@[simp] theorem translateFormula_emb_liftSet
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (φ : SetTheorySemisentence n) :
    translateFormula Ks
        (Rewriting.emb (liftSet φ) :
          Semiproposition (setTemplateLanguage k arities) n) =
      (⌜φ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) := by
  rw [liftSet, ← FirstOrder.Semiformula.lMap_emb, Sentence.typed_quote_def]
  exact translateFormula_lMap_set Ks
    (Rewriting.emb φ : SetTheorySemiproposition n)

/-- Specialization of the embedded membership atom. -/
theorem translate_emb_srcMem
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (t u : ClosedSemiterm (setTemplateLanguage k arities) n) :
    translateFormula Ks
        (Rewriting.emb (srcMem t u) :
          Semiproposition (setTemplateLanguage k arities) n) =
      Bootstrapping.Semiformula.rel Language.Set.Rel.mem
        ![translateTerm (Rew.emb t), translateTerm (Rew.emb u)] := by
  rw [show (Rewriting.emb (srcMem t u) :
        Semiproposition (setTemplateLanguage k arities) n)
      = FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.mem)
          ![Rew.emb t, Rew.emb u] from by
    simp [srcMem]]
  rw [show translateFormula Ks
        (FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.mem)
          ![Rew.emb t, Rew.emb u])
      = Bootstrapping.Semiformula.rel Language.Set.Rel.mem
          (fun i ↦ translateTerm ((![Rew.emb t, Rew.emb u]) i)) from rfl]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Specialization of the embedded equality atom. -/
theorem translate_emb_srcEq
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (t u : ClosedSemiterm (setTemplateLanguage k arities) n) :
    translateFormula Ks
        (Rewriting.emb (srcEq t u) :
          Semiproposition (setTemplateLanguage k arities) n) =
      Bootstrapping.Semiformula.rel Language.Set.Rel.eq
        ![translateTerm (Rew.emb t), translateTerm (Rew.emb u)] := by
  rw [show (Rewriting.emb (srcEq t u) :
        Semiproposition (setTemplateLanguage k arities) n)
      = FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.eq)
          ![Rew.emb t, Rew.emb u] from by
    simp [srcEq]]
  rw [show translateFormula Ks
        (FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.eq)
          ![Rew.emb t, Rew.emb u])
      = Bootstrapping.Semiformula.rel Language.Set.Rel.eq
          (fun i ↦ translateTerm ((![Rew.emb t, Rew.emb u]) i)) from rfl]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Specialization of the embedded `i`-th placeholder atom. -/
theorem translate_emb_srcP
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k)
    (ts : Fin (arities i) → ClosedSemiterm (setTemplateLanguage k arities) n) :
    translateFormula Ks
        (Rewriting.emb (srcP i ts) :
          Semiproposition (setTemplateLanguage k arities) n) =
      (Ks i).subst (fun j ↦ translateTerm (Rew.emb (ts j))) := by
  rw [show (Rewriting.emb (srcP i ts) :
        Semiproposition (setTemplateLanguage k arities) n)
      = FirstOrder.Semiformula.rel (placeholderRel i)
          (fun j ↦ Rew.emb (ts j)) from by
    simp [srcP, Function.comp_def]]
  rw [show translateFormula Ks
        (FirstOrder.Semiformula.rel (placeholderRel i)
          (fun j ↦ Rew.emb (ts j)))
      = (Ks i).subst
          (fun j ↦ translateTerm (Rew.emb (ts (Fin.cast rfl j)))) from rfl]
  simp

end shapes

/-! ## The lifted theory and its compilation -/

/-- `𝗭𝗙𝗖` lifted into the placeholder-enlarged language.  Source proofs over
this theory may mention the placeholders in purely logical steps; every
axiom is placeholder-free. -/
noncomputable def templateZFC (k : ℕ) (arities : Fin k → ℕ) :
    Theory (setTemplateLanguage k arities) :=
  Theory.lMap (setHom k arities) 𝗭𝗙𝗖

/-- Every lifted `𝗭𝗙𝗖` axiom specializes to its own quotation, hence to a
member of the internalized `𝗭𝗙𝗖`.  The shift-fixedness premise is stated on
the raw codes, matching what internal code towers provide. -/
noncomputable def templateZFCTranslation
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, Bootstrapping.shift ℒₛₑₜ (Ks i).val = (Ks i).val) :
    TypedTheoryTemplateTranslation (templateZFC k arities)
      ((𝗭𝗙𝗖 : SetTheory).internalize V) where
  toTypedTemplateTranslation :=
    setTemplateTranslation Ks fun i ↦ Bootstrapping.Semiformula.ext (hKs i)
  axiom_mem := by
    intro σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    change translateFormula Ks
      (Rewriting.emb (τ.lMap (setHom k arities)) :
        Proposition (setTemplateLanguage k arities)) ∈' _
    rw [translateFormula_lMap_set_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff''
      (T := (𝗭𝗙𝗖 : SetTheory))).mpr hτ

/-- Compile a fixed ordinary proof over the lifted `𝗭𝗙𝗖` into a represented
internal `𝗭𝗙𝗖` proof about the chosen model-coded interpretations.  The
result's `.val` is a genuine internal proof code in `V`; the `Ks i` may have
nonstandard formula codes. -/
noncomputable def compileSetTemplate
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, Bootstrapping.shift ℒₛₑₜ (Ks i).val = (Ks i).val)
    {σ : Sentence (setTemplateLanguage k arities)}
    (d : templateZFC k arities ⊢! σ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula Ks (Rewriting.emb σ) :=
  (templateZFCTranslation Ks hKs).compileProof d

/-- The compiled proof's carrier is accepted by `𝗭𝗙𝗖`'s represented proof
predicate. -/
theorem compileSetTemplate_isZFCProof
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, Bootstrapping.shift ℒₛₑₜ (Ks i).val = (Ks i).val)
    {σ : Sentence (setTemplateLanguage k arities)}
    (d : templateZFC k arities ⊢! σ) :
    Proof ((𝗭𝗙𝗖 : SetTheory).internalize V).theory
      (compileSetTemplate Ks hKs d).val
      (translateFormula Ks (Rewriting.emb σ)).val :=
  (templateZFCTranslation Ks hKs).compileProof_isProof d

end LeanProofs.ZFCinPA.SetPlaceholders
