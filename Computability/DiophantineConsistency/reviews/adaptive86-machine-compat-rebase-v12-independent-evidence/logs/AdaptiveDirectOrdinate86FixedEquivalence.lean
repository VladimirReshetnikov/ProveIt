import DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
import DiophantineConsistency.AdaptiveDirectOrdinate86Reverse

/-! Both fixed-port natural zero directions in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86FixedEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Lift
open AdaptiveDirectOrdinate86Reverse AdaptiveDirectOrdinate86FixedForward
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_87_zero_to_86_zero (v : Fin 13 → V)
    (hz : InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 v) :
    ∃ w : Fin 13 → V, InternalZero naturalExpression86 w := by
  let v14 : Fin 14 → V := fun i => if i=13 then v 11+1 else
    if h : i.val<13 then v ⟨i.val,h⟩+1 else 0
  have he : (fun i : Fin 13 => v14 (oldIndex i)) = (fun i => v i+1) := by
    funext i
    fin_cases i <;> simp [v14,oldIndex,embed]
  have hv : ∀i : Fin 13,0<v14 (oldIndex i) := by
    intro i
    rw [show v14 (oldIndex i)=v i+1 by simpa only using congrFun he i]
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87
      (fun j => (currentPorts j:ℤ))) (fun i => v14 (oldIndex i)) := by
    rw [currentPorts_cast,he]
    exact (internalZero_positiveShift AdaptiveFirstRootFactor87Literal.expression87 v).mp hz
  obtain ⟨hb,_,_⟩ := fixed_port_bounds (V:=V)
  obtain ⟨w,hw⟩ := old_positive_zero_to_new_natural86 currentPorts v14 hb hv hz'
  refine ⟨w,?_⟩
  rw [currentPorts_cast] at hw
  exact hw

theorem current_no_zero_iff :
    (∀ v : Fin 13 → V, ¬InternalZero naturalExpression86 v) ↔
    (∀ v : Fin 13 → V, ¬InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 v) := by
  constructor
  · intro h v hv
    obtain ⟨w,hw⟩ := current_87_zero_to_86_zero v hv
    exact h w hw
  · intro h v hv
    obtain ⟨w,hw⟩ := current_86_zero_to_87_zero v hv
    exact h w hw
end DiophantineConsistency.AdaptiveDirectOrdinate86FixedEquivalence
