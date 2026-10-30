import BoundedPAConsistency.TypedTemplateProofCompiler
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# A proof-template placeholder for a model-coded predicate

This module supplies the principal concrete instance of
`TypedTemplateProofCompiler`.  The source language is arithmetic enlarged by
one relation symbol of a fixed arity.  In the target, that relation is
replaced by an arbitrary typed arithmetic formula `S`.

The important point is that `S` is syntax in the ambient arithmetic model;
its code need not be the quotation of a standard Lean formula.  The
translation is nevertheless compatible with negation, quantification,
free-variable shift, and substitution.  A standard proof template mentioning
the placeholder can therefore be compiled into a genuine represented proof
about nonstandard model-coded syntax.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler

/-! ## The one-predicate source language -/

/-- A single relation symbol, inhabited only at the advertised arity. -/
inductive PlaceholderRel (arity : ℕ) : ℕ → Type
  | predicate : PlaceholderRel arity arity
  deriving DecidableEq

noncomputable instance (arity k : ℕ) : Encodable (PlaceholderRel arity k) where
  encode
    | .predicate => 0
  decode x :=
    if hx : x = 0 then
      if hk : k = arity then
        some (hk.symm ▸ PlaceholderRel.predicate)
      else none
    else none
  encodek := by
    intro r
    cases r
    simp

/-- The relational language containing the single placeholder. -/
@[reducible] def placeholderLanguage (arity : ℕ) : Language where
  Func := fun _ ↦ PEmpty
  Rel := PlaceholderRel arity

instance (arity k : ℕ) : DecidableEq ((placeholderLanguage arity).Func k) :=
  fun a _ ↦ nomatch a

instance (arity k : ℕ) : Encodable ((placeholderLanguage arity).Func k) :=
  IsEmpty.toEncodable

instance (arity : ℕ) : (placeholderLanguage arity).DecidableEq where
  func := fun _ ↦ inferInstance
  rel := fun _ ↦ inferInstance

/-- Arithmetic together with one distinguished `arity`-ary relation. -/
@[reducible] def templateLanguage (arity : ℕ) : Language :=
  Language.add ℒₒᵣ (placeholderLanguage arity)

instance (arity : ℕ) : (templateLanguage arity).DecidableEq where
  func := fun k ↦ by
    change DecidableEq ((ℒₒᵣ).Func k ⊕ (placeholderLanguage arity).Func k)
    infer_instance
  rel := fun k ↦ by
    change DecidableEq ((ℒₒᵣ).Rel k ⊕ (placeholderLanguage arity).Rel k)
    infer_instance

/-! ## Translation into typed model-coded arithmetic syntax -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity n m : ℕ}

/-- Interpret source arithmetic terms as typed terms in the ambient model.

The placeholder language has no function symbols, so the `Sum.inr` branch is
empty.  Free-variable indices are embedded as numerals of the model. -/
noncomputable def translateTerm :
    SyntacticSemiterm (templateLanguage arity) n →
      Bootstrapping.Semiterm V ℒₒᵣ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func (Sum.inl f) v => .func f (fun i ↦ translateTerm (v i))
  | .func (Sum.inr f) _ => nomatch f

/-- Replace the placeholder atom by substitution into `S` and retain the
arithmetic and logical constructors literally. -/
noncomputable def translateFormula
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) :
    {n : ℕ} → Semiproposition (templateLanguage arity) n →
      Bootstrapping.Semiformula V ℒₒᵣ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, .rel (Sum.inl r) v =>
      .rel r (fun i ↦ translateTerm (v i))
  | _, .rel (Sum.inr .predicate) v =>
      S.subst (fun i ↦ translateTerm (v i))
  | _, .nrel (Sum.inl r) v =>
      .nrel r (fun i ↦ translateTerm (v i))
  | _, .nrel (Sum.inr .predicate) v =>
      ∼(S.subst (fun i ↦ translateTerm (v i)))
  | _, p ⋏ q => translateFormula S p ⋏ translateFormula S q
  | _, p ⋎ q => translateFormula S p ⋎ translateFormula S q
  | _, ∀⁰ p => ∀⁰ translateFormula S p
  | _, ∃⁰ p => ∃⁰ translateFormula S p

/-! ## Compatibility with rewriting -/

@[simp] theorem translateTerm_shift
    (t : SyntacticSemiterm (templateLanguage arity) n) :
    translateTerm (V := V) (Rew.shift t) =
      (translateTerm (V := V) t).shift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · exact PEmpty.elim f

@[simp] theorem translateTerm_bShift
    (t : SyntacticSemiterm (templateLanguage arity) n) :
    translateTerm (V := V) (Rew.bShift t) =
      (translateTerm (V := V) t).bShift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · exact PEmpty.elim f

@[simp] theorem translateTerm_subst
    (w : Fin n → SyntacticSemiterm (templateLanguage arity) m)
    (t : SyntacticSemiterm (templateLanguage arity) n) :
    translateTerm (V := V) (Rew.subst w t) =
      (translateTerm (V := V) t).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih =>
      rcases f with f | f
      · simp [translateTerm, ih, Matrix.map, Function.comp_def]
      · exact PEmpty.elim f

@[simp] theorem translateFormula_neg
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S (∼p) = ∼translateFormula S p := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | hrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · cases r; simp [translateFormula]
  | hnrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · cases r; simp [translateFormula]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_shift
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S (Rewriting.shift p) =
      (translateFormula S p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.shift_substs, hS,
          Matrix.map, Function.comp_def]
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.shift_substs, hS,
          Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_subst
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (w : Fin n → SyntacticSemiterm (templateLanguage arity) m)
    (p : Semiproposition (templateLanguage arity) n) :
    translateFormula S (Rew.subst w ▹ p) =
      (translateFormula S p).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction p using FirstOrder.Semiformula.rec' generalizing m with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp =>
      simp only [Rewriting.app_all, translateFormula,
        Semiformula.substs_all]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simp [SemitermVec.q, translateTerm_bShift, Matrix.map]
  | hexs p hp =>
      simp only [Rewriting.app_exs, translateFormula,
        Semiformula.substs_ex]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simp [SemitermVec.q, translateTerm_bShift, Matrix.map]

/-- The special `free` operation used by the universal proof rule also
commutes with placeholder specialization. -/
@[simp] theorem translateFormula_free
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S)
    (p : Semiproposition (templateLanguage arity) 1) :
    translateFormula S (Rewriting.free p) =
      (translateFormula S p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst, translateFormula_shift S hS]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-! ## The compiler translation record -/

/-- The concrete syntax translation consumed by the generic template
compiler. -/
noncomputable def modelCodedPredicateTranslation
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S) :
    TypedTemplateTranslation V (templateLanguage arity) ℒₒᵣ where
  term := translateTerm
  formula := translateFormula S
  formula_neg := translateFormula_neg S
  formula_and := fun _ _ ↦ rfl
  formula_or := fun _ _ ↦ rfl
  formula_verum := rfl
  formula_all := fun _ ↦ rfl
  formula_exs := fun _ ↦ rfl
  formula_shift := translateFormula_shift S hS
  formula_free := translateFormula_free S hS
  formula_subst₁ := fun p t ↦ by
    simpa [Matrix.constant_eq_singleton] using
      translateFormula_subst (V := V) S ![t] p

/-! ## Arithmetic proof templates -/

/-- On the arithmetic sublanguage, term specialization is ordinary typed
quotation.  This is the key fact ensuring that a lifted PA axiom remains the
same PA axiom after the placeholder is interpreted. -/
@[simp] theorem translateTerm_lMap_add₁
    (t : SyntacticSemiterm ℒₒᵣ n) :
    translateTerm (V := V)
        (t.lMap (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity))) =
      (⌜t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih =>
      simp only [FirstOrder.Semiterm.lMap_func, Language.Hom.func_add₁,
        translateTerm]
      apply Bootstrapping.Semiterm.ext
      simp [ih, Matrix.map, Function.comp_def]

/-- On formulas which do not mention the placeholder, specialization is
ordinary typed quotation. -/
@[simp] theorem translateFormula_lMap_add₁
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (p : ArithmeticSemiproposition n) :
    translateFormula S
        (p.lMap (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity))) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      simp only [FirstOrder.Semiformula.lMap_rel,
        Language.Hom.rel_add₁, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_add₁, Matrix.map, Function.comp_def]
  | hnrel r v =>
      simp only [FirstOrder.Semiformula.lMap_nrel,
        Language.Hom.rel_add₁, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_add₁, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_lMap_add₁_emb
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (sigma : ArithmeticSentence) :
    translateFormula S
        (Rewriting.emb
          (sigma.lMap
            (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity))) :
          Proposition (templateLanguage arity)) =
      (⌜sigma⌝ : Bootstrapping.Formula V ℒₒᵣ) := by
  rw [← FirstOrder.Semiformula.lMap_emb]
  simpa [Sentence.typed_quote_def] using
    translateFormula_lMap_add₁ S
      (Rewriting.emb sigma : ArithmeticProposition)

/-- PA lifted to the language with one placeholder relation. -/
noncomputable def templatePeano (arity : ℕ) :
    Theory (templateLanguage arity) :=
  Theory.lMap
    (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity)) Peano

/-- A lifted PA proof template may be specialized at an arbitrary closed
model-coded predicate.  Source PA axioms translate back to their ordinary
typed quotations, while the placeholder atoms translate to substitutions
into `S`. -/
noncomputable def modelCodedPredicateTheoryTranslation
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S) :
    TypedTheoryTemplateTranslation (templatePeano arity)
      (Peano.internalize V) where
  toTypedTemplateTranslation := modelCodedPredicateTranslation S hS
  axiom_mem := by
    intro sigma hsigma
    rcases hsigma with ⟨tau, htau, rfl⟩
    change translateFormula S
      (Rewriting.emb
        (tau.lMap
          (Language.Hom.add₁ ℒₒᵣ (placeholderLanguage arity))) :
        Proposition (templateLanguage arity)) ∈'
      (Peano.internalize V).theory
    rw [translateFormula_lMap_add₁_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff'' (T := Peano)).mpr htau

/-- Compile one ordinary proof over lifted PA into a represented PA proof
about the chosen model-coded predicate. -/
noncomputable def compilePeanoTemplate
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S) {sigma : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! sigma) :
    Peano.internalize V ⊢!
      translateFormula S (Rewriting.emb sigma) :=
  (modelCodedPredicateTheoryTranslation S hS).compileProof d

set_option backward.isDefEq.respectTransparency false in
theorem compilePeanoTemplate_isPAProof
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (hS : S.shift = S) {sigma : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! sigma) :
    Proof Peano (compilePeanoTemplate S hS d).val
      (translateFormula S (Rewriting.emb sigma)).val := by
  simpa [compilePeanoTemplate, Proof] using
    (compilePeanoTemplate S hS d).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
