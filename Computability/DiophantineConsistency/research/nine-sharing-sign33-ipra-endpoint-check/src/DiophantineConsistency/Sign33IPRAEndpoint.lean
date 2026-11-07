import DiophantineConsistency.Sign33CurrentJonesSourceIff
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! UNCOMPILED endpoint draft. The first import is a future provider: its
Jones/source existential equivalence provider has not yet been checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33IPRAEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

/-- Jones expression in nine natural model coordinates, using the fixed current seed. -/
def expression : Expr (Fin 9) :=
  ExecutableJones.expression (SharingSeed33.seed CurrentWindowCarry2011.ports) 0

section Model
variable (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Compose the forthcoming Jones and seed/source existential equivalences. -/
theorem zero_iff_current :
    (∃ a : Fin 9 → V, InternalZero expression a) ↔
      ∃ u : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have hleft : (∃ a : Fin 9 → V, InternalZero expression a) ↔
      ∃ a : Fin 9 → V, expression.evalRing (fun i => ι (a i)) = 0 :=
    exists_congr fun a => internalZero_iff expression a
  exact hleft.trans (Sign33CurrentJonesSourceIff.nine_exists_iff_source (V := V))
end Model

/-- Transfer the existing all-model current-equation bridge to this Jones expression. -/
theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge expression := by
  intro V _ _
  have currentBridge : HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=
    fun W _ _ => HACurrentEquation2011.polynomialBridge W
  have hB := currentBridge V
  rw [HAExpressionAssembly.classicalNoZero_iff] at hB ⊢
  rw [← hB]
  simpa only [InternalZero, not_exists, ne_eq] using not_congr (zero_iff_current V)

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

end DiophantineConsistency.Sign33IPRAEndpoint
#print axioms DiophantineConsistency.Sign33IPRAEndpoint.zero_iff_current
#print axioms DiophantineConsistency.Sign33IPRAEndpoint.polynomialBridge
#print axioms DiophantineConsistency.Sign33IPRAEndpoint.native_equivalence
#print axioms DiophantineConsistency.Sign33IPRAEndpoint.standard_equivalence
#print axioms DiophantineConsistency.Sign33IPRAEndpoint.standard_translated_equivalence
