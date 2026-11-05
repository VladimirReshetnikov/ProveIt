import DiophantineConsistency.NineFreshJones
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! # A nine-unknown equation with unconditional iPRA endpoints

Jones's nine-unknowns syntax applied to the quartic gate system of the
maintained CURRENT2011 equation `ObjectCurrentEquation2011.naturalExpression`.
Its zero set in every model of `𝗜𝚺₁` is that of the maintained equation:
`NineFreshJones.jonesModel` (internal Jones), then
`NineLightQuartic.exists_quartic_iff` (quartic gates), then the natural
split. The maintained all-model bridge (`HACurrentEquation2011.polynomialBridge`)
therefore transfers, giving native and standard iPRA proofs
that its no-zero sentence is equivalent to the selected Foundation ZFC
consistency predicate, with no remaining hypothesis.

This equation is different from `ExplicitZFC.expression`, whose source is
the compiled enumerator program (see `IPRAExplicitZFCReduction`); both have
nine unknowns. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANineFreshCurrent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

/-- A local syntax renaming, avoiding a second declaration in the NatExpr namespace. -/
def renameNatural {σ τ : Type*} (f : σ → τ) : NatExpr σ → NatExpr τ
  | .constant a => .constant a
  | .var i => .var (f i)
  | .add p q => .add (renameNatural f p) (renameNatural f q)
  | .mul p q => .mul (renameNatural f p) (renameNatural f q)

/-- Left side of the maintained equation's natural split, over closed witnesses. -/
def left : NatExpr (Empty ⊕ Fin 14) :=
  renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.1

/-- Right side of the maintained equation's natural split. -/
def right : NatExpr (Empty ⊕ Fin 14) :=
  renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.2

/-- The quartic gate system of the maintained equation. -/
def seed : Expr (Fin (QuarticCompiler.witnessCount left right + 1)) :=
  QuarticSyntax.expression left right

/-- **The nine-unknown equation.** -/
def expression : Expr (Fin 9) := ExecutableJones.expression seed 0

theorem evalSemiring_rename {σ τ R : Type*} [Semiring R] (e : NatExpr σ) (f : σ → τ)
    (v : τ → R) : (renameNatural f e).evalSemiring v = e.evalSemiring (v ∘ f) := by
  induction e <;> simp_all [renameNatural, NatExpr.evalSemiring, Function.comp_def]

section Model
variable (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_iff :
    (∃ v : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression v) ↔
      ∃ v : Fin 14 → V, left.evalSemiring (Sum.elim Empty.elim v) =
        right.evalSemiring (Sum.elim Empty.elim v) := by
  simp only [InternalZero, left, right, evalSemiring_rename, Sum.elim_comp_inr]

/-- In every model the nine-unknown equation and the maintained equation have
zeros together. -/
theorem zero_iff_current :
    (∃ a : Fin 9 → V, InternalZero expression a) ↔
      ∃ v : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression v :=
  (NineFreshJones.jonesModel V left right).trans
    ((NineLightQuartic.exists_quartic_iff left right).trans (source_iff V).symm)

end Model

/-- The all-model bridge, transferred from the maintained equation. -/
theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge expression := by
  intro V _ _
  have currentBridge : HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=
    fun W _ _ => HACurrentEquation2011.polynomialBridge W
  have hB := currentBridge V
  rw [HAExpressionAssembly.classicalNoZero_iff] at hB ⊢
  rw [← hB]
  simpa only [InternalZero, not_exists, ne_eq] using not_congr (zero_iff_current V)

/-- **Native iPRA: the nine-unknown equation has no zero iff ZFC is consistent.** -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

/-- The selected Foundation consistency sentence after mapping and GG translation. -/
theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms NineFreshJones.jonesModel
#print axioms polynomialBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms standard_translated_equivalence

end DiophantineConsistency.IPRANineFreshCurrent
