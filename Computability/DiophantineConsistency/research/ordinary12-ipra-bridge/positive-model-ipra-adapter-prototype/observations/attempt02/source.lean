import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.HAExpressionAssembly
import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! A two-way positive model bridge supplies the existing iPRA endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PositiveModelIPRAAdapter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

/-- Every model sees a positive zero exactly when its 215-state machine
halts. This is an explicit two-way hypothesis, not yet a theorem for any
specific compact graph. -/
def PositiveModelBridge {n : ℕ} (e : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ v : Fin n → V, (∀ j,0<v j) ∧ InternalZero e v) ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time)=0

/-- Convert the positive-domain all-model equivalence to the exact
unrestricted zero sentence of the once-shifted expression. -/
theorem bridge_of_positive {n : ℕ} (e : Expr (Fin n)) (hp : PositiveModelBridge e) :
    PolynomialBridge (positiveShift e) := by
  intro V _ _
  rw [classicalNoZero_iff]
  constructor
  · intro h hhalt
    obtain ⟨v,hpos,hzero⟩ := (hp V).mpr hhalt
    let x : Fin n → V := fun j => v j-1
    have hx : (fun j => x j+1)=v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
    have hz : InternalZero (positiveShift e) x := by
      rw [internalZero_positiveShift,hx]
      exact hzero
    exact h x hz
  · intro h v hz
    apply h
    apply (hp V).mp
    refine ⟨fun j => v j+1, ?_, ?_⟩
    · intro j
      exact lt_add_of_nonneg_of_pos (by simp) (by simp)
    · exact (internalZero_positiveShift e v).mp hz

/-- The existing specialized completeness, bounded-refutation and negative
translation pipeline returns an actual native iPRA derivation, provided the
same exact expression has the two-way model bridge above. -/
theorem native_equivalence_of_positive {n : ℕ} (e : Expr (Fin n))
    (hp : PositiveModelBridge e) : nativeTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
        ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge_of_positive e hp)

#print axioms PositiveModelIPRAAdapter.bridge_of_positive
#print axioms PositiveModelIPRAAdapter.native_equivalence_of_positive
end PositiveModelIPRAAdapter
