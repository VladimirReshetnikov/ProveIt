import Mask79ConditionalGuard

/-! A concise sufficient guard inequality for the corrected gauge. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79GuardGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive79Mask Mask79ActualRows Mask79ActualOutput Mask79ModelBridge Mask79NaturalLift Mask79ConditionalGuard
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard_from_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (t : V)
    (hc : q p v*b p v*t < v 2)
    (hg : v 1+v 2 < q p v+b p v*b p v*t) :
    (v 1+b p v*t)+(v 2-q p v*b p v*t)<q p v := by
  have hm : q p v*b p v*t = b p v*t+b p v*b p v*t := by
    unfold q
    ring
  have hs : (v 2-q p v*b p v*t)+(q p v*b p v*t)=v 2 :=
    tsub_add_cancel_of_le (le_of_lt hc)
  apply (add_lt_add_iff_right (b p v*b p v*t)).mp
  calc
    ((v 1+b p v*t)+(v 2-q p v*b p v*t))+b p v*b p v*t =
        v 1+((v 2-q p v*b p v*t)+(b p v*t+b p v*b p v*t)) := by ring
    _ = v 1+((v 2-q p v*b p v*t)+(q p v*b p v*t)) := by rw [←hm]
    _ = v 1+v 2 := by rw [hs]
    _ < q p v+b p v*b p v*t := hg

theorem guarded_zero_of_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (z t : V)
    (hv : ∀ j, 0<v j)
    (hsq : let vv := fun j => ι (v j)
      (shared (integerPorts p) vv (rankTerm (integerPorts p) vv)).sq = ι z)
    (hc : q p v*b p v*t<v 2)
    (hn : (b p v*z+1)*factor p v*t<v 7)
    (hg : v 1+v 2 < q p v+b p v*b p v*t)
    (hz : InternalZero (output79 (integerPorts p)) v) :
    ∃ w : Fin 10 → V, (∀ j, 0<w j) ∧ w 1+w 2<q p w ∧
      InternalZero (output79 (integerPorts p)) w := by
  exact guarded_zero_of_parameter p v z t hv hsq hc hn (guard_from_gap p v t hc hg) hz

#print axioms Mask79GuardGap.guard_from_gap
#print axioms Mask79GuardGap.guarded_zero_of_gap
end Mask79GuardGap
