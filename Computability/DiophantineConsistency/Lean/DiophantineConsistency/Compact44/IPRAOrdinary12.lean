import DiophantineConsistency.Compact44.CompactSymbolicModelUnconditionalIff
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.HAExpressionAssembly

/-! # iPRA endpoints for the 12-variable, 95-operation free-J graph

`CompactSymbolicModelUnconditionalIff.model_iff` (compact44 lane, promoted into
`Compact44/` from `research/ordinary12-ipra-bridge`) proves in every model of
`𝗜𝚺₁` that the literal free-J graph at the symbolic compact44 tuple
`CompactSymbolicModelIff.p` has a positive zero iff machine 215 halts. The
generic adapter below (the argument of
`research/ordinary12-ipra-bridge/positive-model-ipra-adapter-prototype`) turns
this into the polynomial bridge of the once-shifted natural expression, which
the existing pipeline converts into native, standard and equality-only iPRA
equivalences with the selected Foundation ZFC consistency predicate.

Scope: the endpoints are about the Lean literal at the symbolic tuple. Binding
those symbolic coefficients to the retained payload bytes or a PDF is a
separate finite check (see the research directory). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOrdinary12
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

/-- Positive zeros in every model exactly when the machine halts. -/
def PositiveModelBridge {n : ℕ} (e : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ v : Fin n → V, (∀ j, 0 < v j) ∧ InternalZero e v) ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time) = 0

theorem bridge_of_positive {n : ℕ} (e : Expr (Fin n)) (hp : PositiveModelBridge e) :
    PolynomialBridge (positiveShift e) := by
  intro V _ _
  rw [classicalNoZero_iff]
  constructor
  · intro h hhalt
    obtain ⟨v, hpos, hzero⟩ := (hp V).mpr hhalt
    let x : Fin n → V := fun j => v j - 1
    have hx : (fun j => x j + 1) = v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
    have hz : InternalZero (positiveShift e) x := by
      rw [internalZero_positiveShift, hx]
      exact hzero
    exact h x hz
  · intro h v hz
    apply h
    apply (hp V).mp
    refine ⟨fun j => v j + 1, ?_, ?_⟩
    · intro j
      simp
    · exact (internalZero_positiveShift e v).mp hz

/-- The literal free-J graph at the symbolic compact44 tuple. -/
def expression : Expr (Fin 12) :=
  Ordinary12FreeJ.literal CompactSymbolicModelIff.p

theorem positiveBridge : PositiveModelBridge expression :=
  fun V _ _ => CompactSymbolicModelUnconditionalIff.model_iff (V := V)

theorem bridge : PolynomialBridge (positiveShift expression) :=
  bridge_of_positive _ positiveBridge

/-- **Native iPRA: the 12-variable graph has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge

/-- **Standard iPRA.** -/
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

/-- **Equality-only iPRA.** -/
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence

#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAOrdinary12
