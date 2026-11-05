import Absorb88MainRoot
import Absorb88TwoNormGap
import Absorb88FirstQuotient

/-! Draft: derive the two-norm gap from a positive zero of the 88 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88GraphGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open Absorb88TwoNormGap Absorb88FirstQuotient Absorb88MainRoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_gap (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    8*((X*Y)*Y)+4 ≤ v 8+v 9 := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  have hq : 0<q := by dsimp [q]; simp
  have hX : 0<X := mul_pos hq (hv 5)
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hb0 : 0<v 0*(p 0:V) := mul_pos (hv 0) hb
  obtain ⟨tau,_,_,hfirst⟩ := first_root p v hz hb0
  obtain ⟨g,hmain⟩ := main_root p v hv hz
  change tau*tau=1+((X*Y)*Y)*(((X*Y)*Y)+1)*k*k at hfirst
  change g*g=1+ArithmeticPellRecurrence.delta (X*Y+Y)*(v 8+Y*k)*(v 8+Y*k) at hmain
  exact gap X Y k (v 8) (v 9) tau g hX hY (hv 8) (hv 9) rfl hfirst hmain

#print axioms Absorb88GraphGap.graph_gap
end Absorb88GraphGap
