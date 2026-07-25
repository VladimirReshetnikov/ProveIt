import BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.TernaryCongruencePrototype
import BoundedPAConsistency.FinFunext

/-!
# Source-PA proof of the lower successor's existential law

The source language contains an opaque ternary predicate.  Completeness is
therefore used only after the explicit congruence premise has supplied a sound
equality quotient.  In the resulting canonical model, the fixed source
formula evaluates to `SuccessorTruth`, whose existential constructor and
eliminator prove the advertised law immediately at adjacent levels.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSuccessorLaws
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateEqualityQuotient
open LeanProofs.BoundedPAConsistency.TernaryCongruencePrototype

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Focused semantics of the fixed syntax -/

section SourceSemantics

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [Structure.ORing L M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

omit [Nonempty M] hPA in
/-- The equality quotient's canonical expanded structure has the standard
arithmetic reduct on its carrier. -/
private theorem sourceArithmeticReduct_eq_standardModel
    :
    sourceStructure.lMap (arithmeticHom 3 2) =
      LO.FirstOrder.Arithmetic.standardModel M := by
  letI : Structure ℒₒᵣ M :=
    sourceStructure.lMap (arithmeticHom 3 2)
  letI : Structure.ORing ℒₒᵣ M := {
    zero := by
      calc
        (@Semiterm.Operator.Zero.zero ℒₒᵣ _).val ![] =
            (@Semiterm.Operator.Zero.zero L _).val ![] := by
          simp only [Semiterm.Operator.val,
            Semiterm.Operator.Zero.term_eq, Semiterm.val_func]
          congr 1
          funext i
          exact i.elim0
        _ = (0 : M) := Structure.Zero.zero (L := L) (M := M)
    one := by
      calc
        (@Semiterm.Operator.One.one ℒₒᵣ _).val ![] =
            (@Semiterm.Operator.One.one L _).val ![] := by
          simp only [Semiterm.Operator.val,
            Semiterm.Operator.One.term_eq, Semiterm.val_func]
          congr 1
          funext i
          exact i.elim0
        _ = (1 : M) := Structure.One.one (L := L) (M := M)
    add := by
      intro a b
      change Structure.func (L := L)
        (Sum.inl Language.Add.add) ![a, b] = a + b
      exact Structure.Add.add (L := L) (M := M) a b
    mul := by
      intro a b
      change Structure.func (L := L)
        (Sum.inl Language.Mul.mul) ![a, b] = a * b
      exact Structure.Mul.mul (L := L) (M := M) a b
    eq := by
      intro a b
      change Structure.rel (L := L)
        (Sum.inl Language.Eq.eq) ![a, b] ↔ a = b
      exact Structure.Eq.eq (L := L) (M := M) a b
    lt := by
      intro a b
      change Structure.rel (L := L)
        (Sum.inl Language.LT.lt) ![a, b] ↔ a < b
      exact Structure.LT.lt (L := L) (M := M) a b
  }
  exact LO.FirstOrder.Arithmetic.standardModel_unique M
    (sourceStructure.lMap (arithmeticHom 3 2))

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

private def sourceLowerRelation (bound free p : M) : Prop :=
  Structure.rel (L := L)
    (Sum.inr (Sum.inl PlaceholderRel.predicate)) ![bound, free, p]

private noncomputable def sourceLevel (i : Fin 2) : M :=
  Structure.func (L := L)
    (Sum.inr (Sum.inr (ParameterFunc.parameter i))) ![]

include hArithmeticReduct in
private theorem source_one_eq :
    Structure.func (L := L)
      (Sum.inl (Language.One.one : (ℒₒᵣ).Func 0)) ![] = (1 : M) := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      Structure.func (self := s) Language.One.one ![])
    hArithmeticReduct
  exact h

include hArithmeticReduct in
private theorem source_add_eq (a b : M) :
    Structure.func (L := L)
      (Sum.inl (Language.Add.add : (ℒₒᵣ).Func 2)) ![a, b] = a + b := by
  have h := congrArg
    (fun s : Structure ℒₒᵣ M ↦
      Structure.func (self := s) Language.Add.add ![a, b])
    hArithmeticReduct
  exact h

@[simp] private theorem eval_parameterTerm
    (i : Fin 2) (v : Fin n → M) :
    (DynamicTruthTemplateFormula.parameterTerm (n := n) i).valb
        (M := M) v = sourceLevel i := by
  simp [DynamicTruthTemplateFormula.parameterTerm, sourceLevel,
    Matrix.empty_eq]

include hArithmeticReduct in
@[simp] private theorem eval_sourceOne (v : Fin n → M) :
    (sourceOne : ClosedSemiterm L n).valb (M := M) v = 1 := by
  unfold sourceOne
  simp only [FirstOrder.Semiterm.val_func]
  rw [show
    (FirstOrder.Semiterm.val v Empty.elim ∘
      (![] : Fin 0 → ClosedSemiterm L n)) = (![] : Fin 0 → M) by
        funext i
        exact i.elim0]
  exact source_one_eq hArithmeticReduct

include hArithmeticReduct in
@[simp] private theorem eval_sourceLevelSuccessor (v : Fin n → M) :
    (sourceLowerLevelSuccessor : ClosedSemiterm L n).valb (M := M) v =
      sourceLevel 0 + 1 := by
  unfold sourceLowerLevelSuccessor
  simp only [FirstOrder.Semiterm.val_func]
  rw [show
    (FirstOrder.Semiterm.val v Empty.elim ∘
      ![DynamicTruthTemplateFormula.parameterTerm (n := n) 0,
        (sourceOne : ClosedSemiterm L n)]) =
      ![(sourceLevel (M := M) 0 : M), (1 : M)] by
        funext i
        cases i using Fin.cases with
        | zero => exact eval_parameterTerm 0 v
        | succ i =>
            have hi : i = 0 := Fin.eq_zero i
            subst i
            exact eval_sourceOne hArithmeticReduct v]
  exact source_add_eq hArithmeticReduct _ _

include hArithmeticReduct in
@[simp] private theorem eval_liftArithmeticFormula
    (p : ArithmeticSemisentence n) (v : Fin n → M) :
    (liftArithmeticFormula p).Evalb (M := M) v ↔
      p.Evalb (M := M) v := by
  rw [liftArithmeticFormula, Semiformula.eval_lMap]
  exact iff_of_eq <| congrArg
    (fun s : Structure ℒₒᵣ M ↦
      Semiformula.Eval (s := s) v Empty.elim p)
    hArithmeticReduct

@[simp] private theorem eval_apply₃
    (p : Semisentence L 3)
    (t₀ t₁ t₂ : ClosedSemiterm L n) (v : Fin n → M) :
    (DynamicTruthTemplateFormula.apply₃ p t₀ t₁ t₂).Evalb
        (M := M) v ↔
      p.Evalb (M := M)
        ![t₀.valb (M := M) v, t₁.valb (M := M) v,
          t₂.valb (M := M) v] := by
  simp [DynamicTruthTemplateFormula.apply₃,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin3 rfl rfl rfl

@[simp] private theorem eval_apply₂
    (p : Semisentence L 2)
    (t₀ t₁ : ClosedSemiterm L n) (v : Fin n → M) :
    (DynamicTruthTemplateFormula.apply₂ p t₀ t₁).Evalb
        (M := M) v ↔
      p.Evalb (M := M)
        ![t₀.valb (M := M) v, t₁.valb (M := M) v] := by
  simp [DynamicTruthTemplateFormula.apply₂,
    Semiformula.eval_substs, Function.comp_def]
  apply iff_of_eq
  congr 2
  exact funext_fin2 rfl rfl

@[simp] private theorem eval_lowerAtom
    (t₀ t₁ t₂ : ClosedSemiterm L n) (v : Fin n → M) :
    (lowerAtom t₀ t₁ t₂).Evalb (M := M) v ↔
      sourceLowerRelation
        (t₀.valb (M := M) v) (t₁.valb (M := M) v)
        (t₂.valb (M := M) v) := by
  change Structure.rel _ (fun i ↦
      FirstOrder.Semiterm.val v Empty.elim (![t₀, t₁, t₂] i)) ↔
    Structure.rel _
      ![t₀.valb (M := M) v, t₁.valb (M := M) v,
        t₂.valb (M := M) v]
  apply iff_of_eq
  congr 1
  exact funext_fin3 rfl rfl rfl

include hArithmeticReduct in
@[simp] private theorem eval_universalRecordBranch (v : Fin 3 → M) :
    DynamicTruthTemplateFormula.universalRecordBranch.Evalb (M := M) v ↔
      ∃ q < recordFormula (v 2),
        recordFormula (v 2) = ^∀ q ∧
          LowerPiTrue sourceLowerRelation (v 0)
            (recordBound (v 2)) (recordFree (v 2))
            (recordFormula (v 2)) := by
  simp [DynamicTruthTemplateFormula.universalRecordBranch,
    sourceLowerRelation, LowerPiTrue,
    UniversalRecordPrefix, eval_liftArithmeticFormula hArithmeticReduct,
    eval_lowerAtom, Function.comp_def]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_successorRecordValid (v : Fin 2 → M) :
    sourceDerivedSuccessorRecordValid.Evalb (M := M) v ↔
      SigmaRecordValid sourceLowerRelation
        (sourceLevel 0) (sourceLevel 0 + 1) (v 0) (v 1) := by
  simp [sourceDerivedSuccessorRecordValid,
    DynamicTruthTemplateFormula.parameterTerm, sourceLevel,
    SigmaRecordValid, RecordDomain, PositiveRecordBranches,
    eval_liftArithmeticFormula hArithmeticReduct, eval_apply₂, eval_apply₃,
    eval_sourceLevelSuccessor hArithmeticReduct,
    eval_universalRecordBranch hArithmeticReduct]
  aesop

include hArithmeticReduct in
@[simp] private theorem eval_successorTruthFormula (v : Fin 3 → M) :
    sourceDerivedSuccessorTruthFormula.Evalb (M := M) v ↔
      SuccessorTruth sourceLowerRelation (sourceLevel 0) (sourceLevel 0 + 1)
        (v 0) (v 1) (v 2) := by
  simp [sourceDerivedSuccessorTruthFormula,
    sourceLowerRelation, sourceLevel,
    SuccessorTruth, eval_liftArithmeticFormula hArithmeticReduct,
    eval_apply₂, eval_successorRecordValid hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceFormulaDomain (v : Fin 3 → M) :
    sourceFormulaDomain.Evalb (M := M) v ↔
      IsUFormula ℒₒᵣ (v 2) := by
  simp [sourceFormulaDomain,
    eval_liftArithmeticFormula hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceExtendedTruthWitness (v : Fin 4 → M) :
    sourceExtendedTruthWitness.Evalb (M := M) v ↔
      ∃ a, SuccessorTruth sourceLowerRelation
        (sourceLevel 0) (sourceLevel 0 + 1) (v 1 ⁀' a) (v 2) (v 3) := by
  simp [sourceExtendedTruthWitness,
    eval_liftArithmeticFormula hArithmeticReduct, eval_apply₃,
    eval_successorTruthFormula hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceExistentialCodeWitness (v : Fin 3 → M) :
    sourceExistentialCodeWitness.Evalb (M := M) v ↔
      (SuccessorTruth sourceLowerRelation
          (sourceLevel 0) (sourceLevel 0 + 1) (v 0) (v 1) (^∃ (v 2)) ↔
        ∃ a, SuccessorTruth sourceLowerRelation
          (sourceLevel 0) (sourceLevel 0 + 1) (v 0 ⁀' a) (v 1) (v 2)) := by
  simp [sourceExistentialCodeWitness,
    eval_liftArithmeticFormula hArithmeticReduct, eval_apply₂, eval_apply₃,
    eval_successorTruthFormula hArithmeticReduct,
    eval_sourceExtendedTruthWitness hArithmeticReduct]

include hArithmeticReduct in
@[simp] private theorem eval_sourceSuccessorExistentialLawsSentence :
    sourceSuccessorExistentialLawsSentence.Evalb (M := M) ![] ↔
      ExistentialLaws
        (SuccessorTruth sourceLowerRelation
          (sourceLevel (M := M) 0) (sourceLevel (M := M) 0 + 1)) := by
  simp [sourceSuccessorExistentialLawsSentence,
    sourceSuccessorExistentialBody, ExistentialLaws,
    eval_sourceFormulaDomain hArithmeticReduct,
    eval_sourceExistentialCodeWitness hArithmeticReduct]
  constructor
  · intro h bound free q hq
    exact h q free bound hq
  · intro h q free bound hq
    exact h hq

end SourceSemantics

/-! ## Equality-safe source derivation -/

/-- The source theorem with the opaque predicate's congruence requirement
kept as an explicit antecedent.

The successor's upper level is the source term `lowerLevel + 1`, so the
sentence has no separate represented adjacency premise.  This keeps the
compiled proof independent of arithmetic normalization for model-coded
parameters. -/
noncomputable def sourceCongruentSuccessorExistentialLawsSentence :
    Sentence L :=
  placeholderCongruenceSentence 3 2 🡒
    sourceSuccessorExistentialLawsSentence

set_option maxHeartbeats 1600000 in
noncomputable def sourceCongruentSuccessorExistentialLawsProof :
    parameterTemplatePeano 3 2 ⊢!
      sourceCongruentSuccessorExistentialLawsSentence := by
  simpa [sourceCongruentSuccessorExistentialLawsSentence] using
    (complete_underPlaceholderCongruence
      sourceSuccessorExistentialLawsSentence
      (fun X ↦ by
        intro _ _ _ _
        have hArithmeticReduct :=
          sourceArithmeticReduct_eq_standardModel (M := X)
        have hArithmeticPA : X↓[ℒₒᵣ] ⊧* Peano := by
          constructor
          intro sigma hsigma
          rw [← hArithmeticReduct]
          exact Semiformula.models_lMap.mp <|
            (inferInstance : X↓[L] ⊧* parameterTemplatePeano 3 2).models _
              ⟨sigma, hsigma, rfl⟩
        letI : X↓[ℒₒᵣ] ⊧* Peano := hArithmeticPA
        letI : X↓[ℒₒᵣ] ⊧* ISigma 1 :=
          models_of_subtheory hArithmeticPA
        apply (eval_sourceSuccessorExistentialLawsSentence
          hArithmeticReduct).mpr
        intro bound free q hq
        apply SuccessorTruth.exs_iff hq
        simp))

/-! ## Model-coded production specialization -/

section Production

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

private theorem emb_sourceCongruentSuccessorExistentialLawsSentence :
    (Rewriting.emb sourceCongruentSuccessorExistentialLawsSentence :
      Proposition L) =
      Arrow.arrow
        (Rewriting.emb (placeholderCongruenceSentence 3 2) : Proposition L)
        (Rewriting.emb sourceSuccessorExistentialLawsSentence :
          Proposition L) := by
  unfold sourceCongruentSuccessorExistentialLawsSentence
  rw [LogicalConnective.HomClass.map_imply]

/-- Translation preserves just the outer implication of the source theorem.
Recording this small structural equality prevents the production
proof from unfolding the six-binder existential-law body. -/
theorem translate_sourceCongruentSuccessorExistentialLawsSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCongruentSuccessorExistentialLawsSentence) =
      (translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb (placeholderCongruenceSentence 3 2)) 🡒
        successorExistentialLawsFormula lower lowerLevel upperLevel) := by
  rw [emb_sourceCongruentSuccessorExistentialLawsSentence,
    DynamicTruthTemplateFormula.translate_imp]
  rfl

/-- Compile the fixed proof and discharge its explicit congruence premise. -/
noncomputable def compiledSuccessorExistentialLawsProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      successorExistentialLawsFormula lower lowerLevel upperLevel := by
  have hcompiled : Peano.internalize V ⊢!
      translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb sourceCongruentSuccessorExistentialLawsSentence) :=
    compilePeanoTemplate lower ![lowerLevel, upperLevel]
      hlower sourceCongruentSuccessorExistentialLawsProof
  rw [translate_sourceCongruentSuccessorExistentialLawsSentence] at hcompiled
  exact hcompiled ⨀
    translatedOnePredicateCongruenceProof
      lower ![lowerLevel, upperLevel]

/-- PA proves the existential law for every (possibly nonstandard) positive
successor in the represented truth orbit. -/
noncomputable def orbitSuccessorExistentialLawsProof (n : V) :
    Peano.internalize V ⊢!
      successorExistentialLawsFormula
        (DynamicTruthOrbit.truthFormula n) (n + 1) (n + 1 + 1) :=
  compiledSuccessorExistentialLawsProof
    (DynamicTruthOrbit.truthFormula n) (n + 1) (n + 1 + 1)
    (DynamicTruthOrbit.truthFormula_shift n)

end Production

end LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof
