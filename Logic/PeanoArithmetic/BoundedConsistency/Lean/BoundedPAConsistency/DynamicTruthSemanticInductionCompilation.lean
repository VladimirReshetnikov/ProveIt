import BoundedPAConsistency.DynamicTruthSemanticInductionSource
import BoundedPAConsistency.ModelCodedInductionAxiom
import BoundedPAConsistency.FinFunext
import Foundation.FirstOrder.Completeness

/-!
# Compiling the semantic-induction interface

The source sentence from `DynamicTruthSemanticInductionSource` asks for
induction separately at every triple of parameters.  Applying PA induction
directly to that sentence would expose three free parameters, and hence the
nonstandard universal-closure branch of the represented axiom recognizer.

There is a smaller, quotient-safe route.  We put the parameters and both
induction hypotheses *inside* one closed unary predicate `Q(x)`.  Ordinary
induction for `Q` is a shift-fixed represented PA axiom.  Pure first-order
logic then rearranges its quantifiers and implications into the requested
parameterwise induction sentence.  No inspection of the substituted truth
formula is needed.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionCompilation

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionSource
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## A closed unary predicate carrying all parameters -/

/-- The parameter-packed predicate applied to an arbitrary term.  The term
is shifted through the three parameter binders explicitly; defining this
application before the unary predicate avoids leaving delayed substitutions
under opaque truth atoms during semantic normalization. -/
noncomputable def sourceClosedInductionPredicateAt {n : ℕ}
    (x : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  ∀⁰ ∀⁰ ∀⁰
    Arrow.arrow
      (sourceExtendedTruthAt sourceZero (#0) (#1) (#2))
      (Arrow.arrow
        (∀⁰ Arrow.arrow
          (sourceExtendedTruthAt (#0) (#1) (#2) (#3))
          (sourceExtendedTruthAt (sourceSucc (#0)) (#1) (#2) (#3)))
        (sourceExtendedTruthAt
          (Rew.bShift (Rew.bShift (Rew.bShift x)))
          (#0) (#1) (#2)))

/-- `Q(x)` says that, for every `(formula, free, base)`, the usual base and
successor premises imply truth at `base ++ [x]`.

The three quantifiers are ordered so that, in their common body, `base`,
`free`, and `formula` are respectively `#0`, `#1`, and `#2`; the outer
induction variable is `#3`. -/
noncomputable def sourceClosedInductionPredicate :
    Semisentence SourceLanguage 1 :=
  sourceClosedInductionPredicateAt (#0)

/-- The ordinary successor-induction axiom for the closed unary predicate
`sourceClosedInductionPredicate`. -/
noncomputable def sourceClosedInductionAxiom : Sentence SourceLanguage :=
  Arrow.arrow
    (sourceClosedInductionPredicate/[sourceZero])
    (Arrow.arrow
      (∀⁰ Arrow.arrow
        (sourceClosedInductionPredicate/[#0])
        (sourceClosedInductionPredicate/[sourceSucc (#0)]))
      (∀⁰ sourceClosedInductionPredicate/[#0]))

/-- Pure logical bridge from the one closed induction axiom to the original
parameterwise semantic-induction interface. -/
noncomputable def sourceSemanticInductionBridge : Sentence SourceLanguage :=
  Arrow.arrow sourceClosedInductionAxiom sourceSemanticInductionSentence

/-! ## Compact source semantics -/

variable {M : Type*} [sourceStructure : Structure SourceLanguage M]

/-- Regard the still-opaque source truth atom as a four-place relation. -/
private def SourceSat (x base free formula : M) : Prop :=
  sourceExtendedTruthPredicate.Evalb (M := M) ![x, base, free, formula]

/-- The values of the source zero and successor terms.  These names let the
logical bridge remain agnostic about the surrounding arithmetic structure. -/
private def sourceZeroValue : M :=
  sourceZero.valb (M := M) ![]

private def sourceSuccValue (x : M) : M :=
  (sourceSucc (#0)).valb (M := M) ![x]

private def sourceOneValue : M :=
  sourceOne.valb (M := M) ![]

@[simp] private theorem val_sourceZero_raw (v : Fin n → M) :
    sourceZero.valb (M := M) v = sourceZeroValue := by
  simp only [sourceZeroValue, sourceZero,
    FirstOrder.Semiterm.val_func]
  congr 1
  funext i
  exact i.elim0

@[simp] private theorem val_sourceOne_raw (v : Fin n → M) :
    sourceOne.valb (M := M) v = sourceOneValue := by
  simp only [sourceOneValue, sourceOne,
    FirstOrder.Semiterm.val_func]
  congr 1
  funext i
  exact i.elim0

@[simp] private theorem val_sourceSucc_bvar_zero_raw
    (x : M) (v : Fin n → M) :
    (sourceSucc (#0)).valb (M := M) (x :> v) =
      sourceSuccValue x := by
  simp only [sourceSuccValue, sourceSucc, sourceOne,
    FirstOrder.Semiterm.val_func]
  congr 1
  refine funext_fin2 ?_ ?_
  · rfl
  · exact (val_sourceOne_raw (M := M) (x :> v)).trans
      (val_sourceOne_raw (M := M) ![x]).symm

/-- The dependency-light version of four-way application.  The public
semantic module has a stronger theorem specialized to PA models; here only
the substitution environment itself is relevant. -/
private theorem eval_apply₄_raw
    (p : Semisentence SourceLanguage 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm SourceLanguage n)
    (v : Fin n → M) :
    (apply₄ p t₀ t₁ t₂ t₃).Evalb (M := M) v ↔
      p.Evalb (M := M)
        ![t₀.valb (M := M) v, t₁.valb (M := M) v,
          t₂.valb (M := M) v, t₃.valb (M := M) v] := by
  simp [apply₄, Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin4 rfl rfl rfl rfl

@[simp] private theorem eval_sourceExtendedTruthAt_raw
    (x base free formula : ClosedSemiterm SourceLanguage n)
    (v : Fin n → M) :
    (sourceExtendedTruthAt x base free formula).Evalb (M := M) v ↔
      SourceSat
        (x.valb (M := M) v) (base.valb (M := M) v)
        (free.valb (M := M) v) (formula.valb (M := M) v) := by
  simp [sourceExtendedTruthAt, eval_apply₄_raw, SourceSat]

@[simp] private theorem eval_sourceClosedInductionPredicateAt
    (x : ClosedSemiterm SourceLanguage n) (v : Fin n → M) :
    (sourceClosedInductionPredicateAt x).Evalb (M := M) v ↔
      ∀ formula free base,
        SourceSat sourceZeroValue base free formula →
        (∀ y, SourceSat y base free formula →
          SourceSat (sourceSuccValue y) base free formula) →
        SourceSat (x.valb (M := M) v) base free formula := by
  simp [sourceClosedInductionPredicateAt,
    val_sourceZero_raw, val_sourceSucc_bvar_zero_raw,
    FirstOrder.Semiterm.val_bShift]

/-- Substitution into the unary predicate and the explicit application form
have the same semantics.  This lemma lets the source axiom retain the exact
`indBody` syntax expected by the represented PA recognizer without forcing
the completeness proof to normalize rewritings under an opaque truth atom. -/
@[simp] private theorem eval_sourceClosedInductionPredicate_subst
    (t : ClosedSemiterm SourceLanguage n) (v : Fin n → M) :
    (sourceClosedInductionPredicate/[t]).Evalb (M := M) v ↔
      (sourceClosedInductionPredicateAt t).Evalb (M := M) v := by
  simp [sourceClosedInductionPredicate,
    Semiformula.eval_substs,
    eval_sourceClosedInductionPredicateAt,
    Function.comp_def]

set_option maxHeartbeats 1600000 in
/-- The bridge is a fixed first-order derivation.  The lifted PA theory is
present only because this proof will be fed to the standard template
compiler; no nonlogical source axiom is used in the semantic argument. -/
noncomputable def sourceSemanticInductionBridgeProof :
    parameterTemplatePeano 3 2 ⊢! sourceSemanticInductionBridge :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, sourceSemanticInductionBridge,
      sourceClosedInductionAxiom,
      sourceClosedInductionPredicate,
      eval_sourceClosedInductionPredicateAt,
      eval_sourceClosedInductionPredicate_subst,
      sourceSemanticInductionSentence, sourceSemanticInductionBody,
      eval_sourceExtendedTruthAt_raw,
      val_sourceZero_raw, val_sourceSucc_bvar_zero_raw,
      FirstOrder.Semiterm.val_bShift]
    intro _ambient _structure _models hclosed formula free base hzero hstep
    have hQall := hclosed
      (by
        intro formula' free' base' hzero' _hstep'
        exact hzero')
      (by
        intro x hx formula' free' base' hzero' hstep'
        exact hstep' x (hx formula' free' base' hzero' hstep'))
    intro x
    exact hQall x formula free base hzero hstep).get

/-! ## Model-coded specialization -/

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Translation of the closed unary induction predicate after substituting
an arbitrary model-coded ternary truth formula and the two hierarchy levels. -/
noncomputable def closedInductionPredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceClosedInductionPredicate)

/-- Translation of the semantic-induction interface sentence itself. -/
noncomputable def semanticInductionFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![lowerLevel, upperLevel]
    (Rewriting.emb sourceSemanticInductionSentence)

/-! The following three compositional lemmas deliberately keep their source
subformula variable abstract.  This prevents reduction of the large packed
predicate while we translate only the surrounding logical constructors. -/

private theorem translate_sourceArrow {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (p q : Semisentence SourceLanguage n) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb (Arrow.arrow p q)) =
      Arrow.arrow
        (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb p))
        (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb q)) := by
  simp [Semiformula.imp_def,
    ModelCodedPredicateParameters.translateFormula]

private theorem translate_sourceAll {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (p : Semisentence SourceLanguage (n + 1)) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb (∀⁰ p)) =
      ∀⁰ translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb p) := by
  simp [ModelCodedPredicateParameters.translateFormula]

private theorem translate_sourceSubstOne {n : ℕ}
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (p : Semisentence SourceLanguage 1)
    (t : ClosedSemiterm SourceLanguage n) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb (p/[t])) =
      (translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb p)).subst
          ![translateTerm ![lowerLevel, upperLevel]
            (Rew.emb t : SyntacticSemiterm SourceLanguage n)] := by
  rw [Rewriting.emb_subst_eq_subst_coe₁,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- The canonical source induction axiom translates literally to the typed
`indBody` consumed by `paInductionProofOfShiftFixed`. -/
@[simp] theorem translate_sourceClosedInductionAxiom
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceClosedInductionAxiom) =
      indBody
        (closedInductionPredicateFormula lower lowerLevel upperLevel) := by
  simp only [sourceClosedInductionAxiom, indBody,
    translate_sourceArrow, translate_sourceAll,
    translate_sourceSubstOne]
  unfold closedInductionPredicateFormula
  have hzero :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (sourceZero (n := 0)) :
            SyntacticSemiterm SourceLanguage 0) =
        (Arithmetic.typedNumeral 0 :
          Bootstrapping.Semiterm V ℒₒᵣ 0) := by
    ext
    simp [sourceZero,
      ModelCodedPredicateParameters.translateTerm,
      Arithmetic.typedNumeral]
  have hvar :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (#0 : ClosedSemiterm SourceLanguage 1) :
            SyntacticSemiterm SourceLanguage 1) =
        (Bootstrapping.Semiterm.bvar 0 :
          Bootstrapping.Semiterm V ℒₒᵣ 1) := by
    rfl
  have hsucc :
      translateTerm ![lowerLevel, upperLevel]
          (Rew.emb (sourceSucc (#0) :
            ClosedSemiterm SourceLanguage 1) :
              SyntacticSemiterm SourceLanguage 1) =
        (Bootstrapping.Semiterm.bvar 0 + Arithmetic.typedNumeral 1 :
          Bootstrapping.Semiterm V ℒₒᵣ 1) := by
    ext
    simp [sourceSucc, sourceOne,
      ModelCodedPredicateParameters.translateTerm,
      Arithmetic.typedNumeral, Arithmetic.add]
  rw [hzero, hvar, hsucc]
  simp

/-! ## Compiled PA proof -/

/-- The packed unary predicate is closed whenever the substituted lower
truth formula is closed.  The proof reasons through source translation, so
it remains valid even when `lower` is nonstandard model-coded syntax. -/
@[simp] theorem closedInductionPredicateFormula_shift
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (hlower : lower.shift = lower) :
    (closedInductionPredicateFormula
      lower lowerLevel upperLevel).shift =
      closedInductionPredicateFormula lower lowerLevel upperLevel := by
  unfold closedInductionPredicateFormula
  rw [← translateFormula_shift
    lower ![lowerLevel, upperLevel] hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Literal translation of the pure source bridge. -/
@[simp] theorem translate_sourceSemanticInductionBridge
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceSemanticInductionBridge) =
      Arrow.arrow
        (indBody
          (closedInductionPredicateFormula
            lower lowerLevel upperLevel))
        (semanticInductionFormula lower lowerLevel upperLevel) := by
  simp only [sourceSemanticInductionBridge,
    translate_sourceArrow, translate_sourceClosedInductionAxiom,
    semanticInductionFormula]

/-- Compile the fixed pure-logic bridge at arbitrary model-coded truth
syntax. -/
noncomputable def compiledSemanticInductionBridge
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      Arrow.arrow
        (indBody
          (closedInductionPredicateFormula
            lower lowerLevel upperLevel))
        (semanticInductionFormula lower lowerLevel upperLevel) := by
  simpa only [translate_sourceSemanticInductionBridge] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel]
      hlower sourceSemanticInductionBridgeProof)

/-- PA proves the represented semantic-induction interface.  The only
arithmetic axiom used beyond the compiled pure bridge is ordinary induction
for the closed packed predicate. -/
noncomputable def semanticInductionFormulaProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V)
    (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      semanticInductionFormula lower lowerLevel upperLevel :=
  TProof.modusPonens
    (compiledSemanticInductionBridge
      lower lowerLevel upperLevel hlower)
    (paInductionProofOfShiftFixed
      (closedInductionPredicateFormula lower lowerLevel upperLevel)
      (congrArg Bootstrapping.Semiformula.val
        (closedInductionPredicateFormula_shift
          lower lowerLevel upperLevel hlower)))

end LeanProofs.BoundedPAConsistency.DynamicTruthSemanticInductionCompilation
