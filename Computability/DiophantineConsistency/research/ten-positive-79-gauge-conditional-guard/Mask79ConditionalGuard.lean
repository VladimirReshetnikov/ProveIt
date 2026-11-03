import Mask79NaturalLiftV2

/-! Square representation and conditional guarded zero from a supplied parameter. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mask79ConditionalGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive79Mask Mask79ActualRows Mask79ActualOutput Mask79ModelBridge Mask79NaturalLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem square_represented (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    ∃ z : V, let vv := fun j => ι (v j)
      (shared (integerPorts p) vv (rankTerm (integerPorts p) vv)).sq = ι z := by
  apply nonneg_iff.mp
  unfold shared
  exact mul_self_nonneg _

theorem guarded_zero_of_parameter (p : Fin 4 → ℕ) (v : Fin 10 → V) (z t : V)
    (hv : ∀ j, 0<v j)
    (hsq : let vv := fun j => ι (v j)
      (shared (integerPorts p) vv (rankTerm (integerPorts p) vv)).sq = ι z)
    (hc : q p v*b p v*t<v 2)
    (hn : (b p v*z+1)*factor p v*t<v 7)
    (hg : (v 1+b p v*t)+(v 2-q p v*b p v*t)<q p v)
    (hz : InternalZero (output79 (integerPorts p)) v) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ w 1+w 2<q p w ∧
      InternalZero (output79 (integerPorts p)) w := by
  refine ⟨moved p v z t, moved_positive p v z t hv hc hn, ?_, ?_⟩
  · exact hg
  · exact zero_preserved_of_lift p v (moved p v z t) (ι t)
      (moved_lift p v z t hsq hc hn) hz

#print axioms Mask79ConditionalGuard.square_represented
#print axioms Mask79ConditionalGuard.guarded_zero_of_parameter
end Mask79ConditionalGuard
