import DiophantineConsistency.AdaptiveAQ31ConditionalNoZero
import DiophantineConsistency.IPRAAQ32Native
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRAAQ31ConditionalBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open AdaptiveEquationSyntax2011 HAExpressionAssembly FoundationHANoZero

def MachineOrients : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ time : V, first (ArithmeticMachineRun215.run time) = 0) →
    ∃ v : Fin 32 → V, (∀ i, 0 < v i) ∧ v 24 < v 23 ∧
      InternalZero (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports) v

theorem sameNoZero_of_machineOrients (h : MachineOrients) :
    HAExpressionNoZeroEquiv.SameNoZero
      (positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports))
      IPRAAQ32Native.literalNatural := by
  intro V _ _
  apply AdaptiveAQ31ConditionalNoZero.shifted_no_zero_iff_of_orient
  rintro ⟨v, hv, hz⟩
  have hshift : InternalZero IPRAAQ32Native.literalNatural (fun i => v i - 1) := by
    change InternalZero (positiveShift (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports)) _
    rw [internalZero_positiveShift]
    have he : (fun i => (v i - 1) + 1) = v := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hv i))
    rw [he]
    exact hz
  have hhalt : ∃ time : V, first (ArithmeticMachineRun215.run time) = 0 := by
    by_contra hnot
    have hmodel := (IPRAAQ32Native.bridge32 V).mpr hnot
    have hnz := (classicalNoZero_iff IPRAAQ32Native.literalNatural).mp hmodel
    exact hnz (fun i => v i - 1) hshift
  exact h V hhalt
theorem bridge31_of_machineOrients (h : MachineOrients) :
    PolynomialBridge (positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports)) :=
  HAExpressionNoZeroEquiv.bridge _ _ (sameNoZero_of_machineOrients h) IPRAAQ32Native.bridge32

theorem conditional_native (h : MachineOrients) :
    IPRANativeTheory.nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports)) 🡘
        ∼IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge31_of_machineOrients h)
#print axioms sameNoZero_of_machineOrients
#print axioms bridge31_of_machineOrients
#print axioms conditional_native
end DiophantineConsistency.IPRAAQ31ConditionalBridge
