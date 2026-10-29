import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
namespace AdaptiveModFourProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#check zero_or_succ
#check lt_succ_iff_le
#check le_iff_eq_or_lt
#check mod_add
#check mod_mul
#check mod_lt
#check mod_eq_self_of_lt
#check ZMod.natCast_self
#check ZMod.natCast_eq_natCast_iff
#check ZMod.val
#check ZMod.val_add
#check ZMod.val_mul
#check Int.cast_ofNat
#check eq_nat_of_lt_nat
#check Nat.cast_mod
#check Nat.cast_add
#check Nat.cast_mul
#check Nat.cast_inj
#check ZMod.natCast_mod
#check ZMod.natCast_eq_natCast_iff
#check ZMod.intCast_zmod_eq_zero_iff_dvd
