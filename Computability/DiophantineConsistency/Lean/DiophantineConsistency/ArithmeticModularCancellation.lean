import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Mathlib.Tactic.Ring

/-! Cancellation of a common offset modulo a positive modulus in an IΣ1 model. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticModularCancellation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem add_cancel {a b c m : V} (hm : 0 < m) (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  have hr := le_of_lt (mod_lt c hm)
  have hc : c+(m-c%m)=m*(c/m+1) := by
    calc
      c+(m-c%m)=(m*(c/m)+c%m)+(m-c%m) := by rw [div_add_mod]
      _=m*(c/m)+(c%m+(m-c%m)) := by ring
      _=m*(c/m)+m := by rw [add_tsub_cancel_of_le hr]
      _=m*(c/m+1) := by ring
  have hh : ((a+c)+(m-c%m))%m=((b+c)+(m-c%m))%m := by
    rw [mod_add (a:=a+c) hm,mod_add (a:=b+c) hm,h]
  simpa only [add_assoc,hc,mod_add_mul' _ _ hm] using hh

end DiophantineConsistency.ArithmeticModularCancellation
