import DiophantineConsistency.AdaptiveQV42ConditionalNoZero
import DiophantineConsistency.IPRAZ43Native
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRAQV42ConditionalBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open AdaptiveEquationSyntax2011 HAExpressionAssembly FoundationHANoZero

def MachineOrients : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ time : V, first (ArithmeticMachineRun215.run time) = 0) →
    ∃ v : Fin 43 → V, (∀ i, 0 < v i) ∧ v 26 < v 25 ∧
      InternalZero (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports) v

theorem sameNoZero_of_machineOrients (h : MachineOrients) :
    HAExpressionNoZeroEquiv.SameNoZero
      (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports))
      IPRAZ43Native.literalNatural := by
  intro V _ _
  apply AdaptiveQV42ConditionalNoZero.shifted_no_zero_iff_of_orient
  rintro ⟨v, hv, hz⟩
  have hshift : InternalZero IPRAZ43Native.literalNatural (fun i => v i - 1) := by
    change InternalZero (positiveShift (AdaptiveZ43Context.literal CurrentWindowCarry2011.ports)) _
    rw [internalZero_positiveShift]
    have he : (fun i => (v i - 1) + 1) = v := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv i))
    rw [he]
    exact hz
  have hhalt : ∃ time : V, first (ArithmeticMachineRun215.run time) = 0 := by
    by_contra hnot
    have hmodel := (IPRAZ43Native.bridge43 V).mpr hnot
    have hnz := (classicalNoZero_iff IPRAZ43Native.literalNatural).mp hmodel
    exact hnz (fun i => v i - 1) hshift
  exact h V hhalt
theorem bridge42_of_machineOrients (h : MachineOrients) :
    PolynomialBridge (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports)) :=
  HAExpressionNoZeroEquiv.bridge _ _ (sameNoZero_of_machineOrients h) IPRAZ43Native.bridge43

theorem conditional_native (h : MachineOrients) :
    IPRANativeTheory.nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveQV42Context.literal CurrentWindowCarry2011.ports)) 🡘
        ∼IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge42_of_machineOrients h)
#print axioms sameNoZero_of_machineOrients
#print axioms bridge42_of_machineOrients
#print axioms conditional_native
end DiophantineConsistency.IPRAQV42ConditionalBridge
