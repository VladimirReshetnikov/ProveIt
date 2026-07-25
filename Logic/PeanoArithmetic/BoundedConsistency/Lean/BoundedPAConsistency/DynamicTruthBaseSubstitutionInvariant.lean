import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.FixedLevelTruthSubstitution
import BoundedPAConsistency.FinFunext

/-!
# A genuine PA proof of base substitution invariance

At the base of the dynamic truth orbit, the upper truth predicate is the
typed quotation of the ordinary first-level partial-truth formula.  Hence the
seven-variable simultaneous-substitution certificate field itself comes from
one ordinary arithmetic sentence.  We construct that sentence here, identify
its quotation with the pre-existing model-coded base field, prove it in outer
PA using fixed-level substitution at external level zero, and apply D1 to
obtain the actual internal PA derivation.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthSubstitution

/-! ## Ordinary seven-variable syntax -/

/-- Apply an ordinary closed five-place formula to five ordinary terms. -/
noncomputable def standardApply₅ {n : ℕ}
    (S : ArithmeticSemisentence 5)
    (t₀ t₁ t₂ t₃ t₄ : ClosedSemiterm ℒₒᵣ n) :
    ArithmeticSemisentence n :=
  S ⇜ ![t₀, t₁, t₂, t₃, t₄]

/-- Quotation commutes with the five-place application used for the named
substitution-environment predicate. -/
@[simp] theorem typedQuote_standardApply₅
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
    {n : ℕ} (S : ArithmeticSemisentence 5)
    (t₀ t₁ t₂ t₃ t₄ : ClosedSemiterm ℒₒᵣ n) :
    (⌜standardApply₅ S t₀ t₁ t₂ t₃ t₄⌝ :
        Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜S⌝ : Bootstrapping.Semiformula V ℒₒᵣ 5).subst
        ![(⌜t₀⌝ : Bootstrapping.Semiterm V ℒₒᵣ n),
          (⌜t₁⌝ : Bootstrapping.Semiterm V ℒₒᵣ n),
          (⌜t₂⌝ : Bootstrapping.Semiterm V ℒₒᵣ n),
          (⌜t₃⌝ : Bootstrapping.Semiterm V ℒₒᵣ n),
          (⌜t₄⌝ : Bootstrapping.Semiterm V ℒₒᵣ n)] := by
  rw [standardApply₅, typedQuote_closedSubst]
  congr
  exact funext_fin5 rfl rfl rfl rfl rfl

/-- The substituting vector is an arity-long vector of terms admitting the
displayed number of bound variables. -/
noncomputable def standardBaseSemitermVectorFormula :
    ArithmeticSemisentence 7 :=
  standardApply₃ (isSemitermVec ℒₒᵣ).sigma.val (#0) (#3) (#4)

/-- The term-bound parameter is the length of the original bound
environment. -/
noncomputable def standardBaseBoundLengthFormula :
    ArithmeticSemisentence 7 :=
  standardApply₂ lhDef.val (#3) (#1)

/-- The supplied environments realize evaluation of every term in the
simultaneous-substitution vector. -/
noncomputable def standardBaseSubstitutionEnvironmentFormula :
    ArithmeticSemisentence 7 :=
  standardApply₅ isSubstitutionEnvironmentDef.val
    (#1) (#2) (#0) (#4) (#5)

/-- The original code is a semiformula with the displayed arity. -/
noncomputable def standardBaseSemiformulaFormula :
    ArithmeticSemisentence 7 :=
  standardApply₂ (isSemiformula ℒₒᵣ).sigma.val (#0) (#6)

/-- The original formula code is bounded at external hierarchy level zero. -/
noncomputable def standardBaseSubstitutionBoundedDomainFormula :
    ArithmeticSemisentence 7 :=
  standardApply₂ (quantifierBoundedCodeDef ℒₒᵣ).val
    (‘0’ : ArithmeticSemiterm Empty 7) (#6)

/-- A represented substituted code whose first-level truth agrees with truth
of the original formula in the substitution environment.  Under the witness
binder, `#0` is the substituted code, `#5` the term vector, and `#7` the
original formula. -/
noncomputable def standardBaseSubstitutedTruthWitnessFormula :
    ArithmeticSemisentence 7 :=
  ∃⁰
    (standardApply₃ (substsGraph ℒₒᵣ).val (#0) (#5) (#7) ⋏
      LogicalConnective.iff
        (standardApply₃ levelZeroTruthSyntax (#2) (#3) (#0))
        (standardApply₃ levelZeroTruthSyntax (#6) (#3) (#7)))

/-- The complete ordinary simultaneous-substitution implication for fixed
inputs. -/
noncomputable def standardBaseSubstitutionInvariantBody :
    ArithmeticSemisentence 7 :=
  Arrow.arrow
    (standardBaseSemitermVectorFormula ⋏
      (standardBaseBoundLengthFormula ⋏
        (standardBaseSubstitutionEnvironmentFormula ⋏
          (standardBaseSemiformulaFormula ⋏
            standardBaseSubstitutionBoundedDomainFormula))))
    standardBaseSubstitutedTruthWitnessFormula

/-- Universal closure of all seven inputs, in the same de Bruijn order as
`baseSubstitutionInvariantFormula`. -/
noncomputable def standardBaseSubstitutionInvariantSentence :
    ArithmeticSentence :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ standardBaseSubstitutionInvariantBody

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The standard sentence quotes literally to the existing model-coded base
field.  In particular, both truth occurrences quote to
`levelZeroTruthFormula`; no semantic equivalence is used in this bridge. -/
@[simp] theorem typedQuote_standardBaseSubstitutionInvariantSentence :
    (⌜standardBaseSubstitutionInvariantSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      baseSubstitutionInvariantFormula := by
  simp [standardBaseSubstitutionInvariantSentence,
    standardBaseSubstitutionInvariantBody,
    standardBaseSemitermVectorFormula,
    standardBaseBoundLengthFormula,
    standardBaseSubstitutionEnvironmentFormula,
    standardBaseSemiformulaFormula,
    standardBaseSubstitutionBoundedDomainFormula,
    standardBaseSubstitutedTruthWitnessFormula,
    baseSubstitutionInvariantFormula_eq_upper,
    upperSubstitutionInvariantFormula,
    semitermVectorFormula, boundLengthFormula,
    substitutionEnvironmentFormula, semiformulaFormula,
    boundedDomainFormula, substitutedTruthWitnessFormula,
    DynamicTruthFormula.apply₃,
    DynamicTruthFormula.levelZeroTruthFormula_eq_typedQuote]

/-! ## Outer and internal PA derivations -/

/-- Outer PA proves the ordinary base substitution field.  In each PA model,
the represented graph produces the actual code `subst terms p`, and the
fixed-level simultaneous-substitution theorem at level zero proves the two
first-level truth assertions equivalent. -/
noncomputable def standardBaseSubstitutionInvariantProof :
    Peano ⊢! standardBaseSubstitutionInvariantSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseSubstitutionInvariantSentence,
      standardBaseSubstitutionInvariantBody,
      standardBaseSemitermVectorFormula,
      standardBaseBoundLengthFormula,
      standardBaseSubstitutionEnvironmentFormula,
      standardBaseSemiformulaFormula,
      standardBaseSubstitutionBoundedDomainFormula,
      standardBaseSubstitutedTruthWitnessFormula,
      standardApply₅, standardApply₂, standardApply₃]
    intro p subBound terms termBound free bound arity
      hterms hboundLength henvironment hformula hbounded
    have hbounded' : QuantifierBoundedCode ℒₒᵣ
        (levelCode (V := M) 0) p := by
      apply OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mpr
      simpa [levelCode] using hbounded
    simpa [eval_levelZeroTruthSyntax_iff, levelCode] using
      (sigmaTrue_succ_subst_iff_of_isSubstitutionEnvironment
        (V := M) 0 hterms hboundLength.symm henvironment
        hformula hbounded')).get

/-- D1 transports the standard PA theorem to a genuine derivation of the
exact base model-coded certificate field. -/
noncomputable def baseSubstitutionInvariantProof :
    Peano.internalize V ⊢! baseSubstitutionInvariantFormula := by
  rw [← typedQuote_standardBaseSubstitutionInvariantSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseSubstitutionInvariantSentence from
      ⟨standardBaseSubstitutionInvariantProof⟩)).get

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseSubstitutionInvariant
