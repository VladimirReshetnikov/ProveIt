import DiophantineConsistency.AdaptiveDirectOrdinate86RankBoundCompat
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
import DiophantineConsistency.AdaptiveDirectOrdinate86Forward

/-! Fixed-port 86-zero to 87-zero direction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Forward
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_port_bounds : 0<(currentPorts 0:V) ∧
    (currentPorts 2:V)<(currentPorts 0:V) ∧
    (currentPorts 3:V)<2*(currentPorts 0:V) := by
  obtain ⟨hb,hl,hh⟩ := ArithmeticAdaptiveRankWindow2011.current_bounds_nat
  have hb' : 0<currentPorts 0 := by
    simpa only [currentPorts,Matrix.cons_val_zero] using (show 0<CurrentMasks2011.beta by omega)
  have hl' : currentPorts 2<currentPorts 0 := by
    change CurrentMasks2011.lowPort<CurrentMasks2011.beta
    exact hl
  have hh' : currentPorts 3<2*currentPorts 0 := by
    change CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta
    exact hh
  exact ⟨by exact_mod_cast hb',by exact_mod_cast hl',by exact_mod_cast hh'⟩

theorem current_86_zero_to_87_zero (v : Fin 13 → V)
    (hz : InternalZero naturalExpression86 v) :
    ∃ w : Fin 13 → V, InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 w := by
  let v14 : Fin 14 → V := fun i => if h : i.val<13 then v ⟨i.val,h⟩+1 else 0
  have he : (fun i : Fin 13 => v14 (embed i)) = (fun i => v i+1) := by
    funext i
    simp [v14,embed]
  have hv : ∀i : Fin 13,0<v14 (embed i) := by
    intro i
    rw [show v14 (embed i)=v i+1 by simpa only using congrFun he i]
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hz' : InternalZero (expressionAt86 (fun j => (currentPorts j:ℤ))) (fun i => v14 (embed i)) := by
    rw [currentPorts_cast,he]
    exact (internalZero_positiveShift expression86 v).mp hz
  obtain ⟨hb,hl,hh⟩ := fixed_port_bounds (V:=V)
  obtain ⟨w,hw⟩ := new_positive_zero_to_old_natural86 currentPorts v14 hb hl hh hv hz'
  refine ⟨w,?_⟩
  rw [currentPorts_cast] at hw
  exact hw
end DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
