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

/-- Reducing modulo a multiple does not change the residue modulo its divisor. -/
theorem mod_mod_of_dvd {m n : V} (hm : 0 < m) (h : m ∣ n) (a : V) : a % n % m = a % m := by
  conv_rhs => rw [← div_add_mod a n]
  rw [mod_add_remove_left_of_dvd (dvd_mul_of_dvd_left h _) hm]

/-- Scaling a residue and its modulus by the same positive factor. -/
theorem mul_mod_mul {k a b : V} (hk : 0 < k) (hb : 0 < b) :
    (k * a) % (k * b) = k * (a % b) := by
  have he : k * a = (k * b) * (a / b) + k * (a % b) := by
    calc k * a = k * (b * (a / b) + a % b) := by rw [div_add_mod]
      _ = _ := by ring
  have hr : k * (a % b) < k * b := mul_lt_mul_of_pos_left (mod_lt _ hb) hk
  rw [he, mod_mul_add' _ _ (mul_pos hk hb), mod_eq_self_of_lt hr]

end DiophantineConsistency.ArithmeticModularCancellation
