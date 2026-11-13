import DiophantineConsistency.ExplicitZFCSyntax
import DiophantineConsistency.ArithmeticCheckerMachine215
import DiophantineConsistency.IPRAQuarticModelBridge
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! # iPRA endpoints for the nine-variable equation from two model obligations

`ExplicitZFCSyntax.expression` is the closed nine-variable equation of
`ExplicitZFC` (`ExplicitZFC.expression_eq_syntax`). Its no-zero sentence is
provably equivalent in native, standard and equality-only iPRA to the
selected Foundation ZFC consistency predicate once two statements about
arbitrary models of `𝗜𝚺₁` hold:

* `JonesModel`: Jones's nine-unknowns reduction, internally and uniformly in
  the quartic seed — the nine-variable syntax built from a quartic gate
  system has an internal zero iff the gate system does;
* `SourceModel`: the compiled source equation of the enumerator program
  holds at some internal witness iff the model's internal C222 proof
  enumerator, started from the literal state `⟨0,4,0,…⟩`, halts.

Everything else is already internal: the quartic gate stage
(`IPRAQuarticModelBridge.exists_quartic_iff`), the C222 checker soundness
and completeness (`ArithmeticEnumSoundnessPerm222`) and its agreement with
the decimal 215 machine (`ArithmeticCheckerMachine215`). No ZFC calibration
is needed: `haltingTest` runs the same enumerator from the same state.
Both obligations are explicit hypotheses here, not axioms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAExplicitZFCReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- The closed source representation of the enumerator program. -/
abbrev source := ExplicitZFCSyntax.representation

/-- The number of source witnesses retained after compaction. -/
abbrev sourceCount : ℕ :=
  WitnessCompaction.count (SimplifiedJones.left source) (SimplifiedJones.right source)

/-- Left side of the compacted natural source equation. -/
abbrev left : NatExpr (Empty ⊕ Fin sourceCount) := CompactedJones.left source

/-- Right side of the compacted natural source equation. -/
abbrev right : NatExpr (Empty ⊕ Fin sourceCount) := CompactedJones.right source

/-- Jones's nine-unknowns reduction in every model of `𝗜𝚺₁`, uniformly in
the quartic gate system. -/
def JonesModel : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)),
    (∃ a : Fin 9 → V,
      InternalZero (ExecutableJones.expression (QuarticSyntax.expression p q) 0) a) ↔
      ∃ v : Fin (QuarticCompiler.witnessCount p q + 1) → V,
        InternalZero (QuarticSyntax.expression p q) v

/-- The compiled source equation holds internally iff the internal C222
enumerator halts from the literal initial state. -/
def SourceModel : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ w : Fin sourceCount → V,
      left.evalSemiring (Sum.elim Empty.elim w) = right.evalSemiring (Sum.elim Empty.elim w)) ↔
      ∃ time : V, ArithmeticEnumRunPerm222.run time (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0

theorem expression_eq : ExplicitZFCSyntax.expression =
    ExecutableJones.expression (QuarticSyntax.expression left right) 0 := rfl

/-- In each model, an internal zero exists iff the decimal 215 machine halts. -/
theorem zero_iff_halts (hJ : JonesModel) (hS : SourceModel)
    (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (∃ a : Fin 9 → V, InternalZero ExplicitZFCSyntax.expression a) ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time) = 0 := by
  rw [expression_eq]
  exact (hJ V left right).trans <|
    (IPRAQuarticModelBridge.exists_quartic_iff left right).trans <|
      (hS V).trans <|
        (ArithmeticEnumSoundnessPerm222.refutation_iff_zero_work_halts (V := V)).symm.trans
          (ArithmeticCheckerMachine215.refutation_iff_blank_halts (V := V))

/-- The all-model bridge required by the generic iPRA assembly. -/
theorem bridge (hJ : JonesModel) (hS : SourceModel) :
    HAExpressionAssembly.PolynomialBridge ExplicitZFCSyntax.expression := by
  intro V _ _
  rw [HAExpressionAssembly.classicalNoZero_iff, ← zero_iff_halts hJ hS V]
  simp only [InternalZero, not_exists, ne_eq]

/-- **Native iPRA**, under the two model obligations. -/
theorem native_equivalence (hJ : JonesModel) (hS : SourceModel) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge hJ hS)

/-- **Standard iPRA**, under the two model obligations. -/
theorem standard_equivalence (hJ : JonesModel) (hS : SourceModel) :
    IPRAStandardTheory.standardTheory ⊢
      IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression 🡘
        ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (native_equivalence hJ hS)

/-- **Equality-only iPRA**, under the two model obligations. -/
theorem reference_equivalence (hJ : JonesModel) (hS : SourceModel) :
    IPRAEqualityOnlyReference.referenceTheory ⊢
      IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression) 🡘
        ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference (native_equivalence hJ hS)

end DiophantineConsistency.IPRAExplicitZFCReduction
