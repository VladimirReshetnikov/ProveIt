import DiophantineConsistency.ControllerPowerCoordinates
import DiophantineConsistency.CurrentAuxiliaryOrder2011

/-! Full-modulus order and affine power coordinates for the literal current
controller. Fixed-factor congruences and the auxiliary prime-power order
are proved inputs, not supplied orbit or coordinate assumptions. -/
namespace DiophantineConsistency.CurrentPowerCoordinates2011

open CurrentControllerData2011 CurrentAuxiliaryOrder2011
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

attribute [local irreducible] CurrentControllerData2011.B

/-- Actual CRT preserves order as the least common multiple of both orders. -/
theorem order_product {a b : ℕ} (hab : Nat.Coprime a b) (x k : ℕ) :
    orderOf ((x : ZMod (a*b))^k) =
      Nat.lcm (orderOf ((x : ZMod a)^k)) (orderOf ((x : ZMod b)^k)) := by
  calc
    _ = orderOf (ZMod.chineseRemainder hab ((x : ZMod (a*b))^k)) :=
      ((ZMod.chineseRemainder hab).toMulEquiv.orderOf_eq _).symm
    _ = _ := by rw [map_pow, map_natCast]; exact Prod.orderOf_mk

theorem generator_cast_47 : (B : ZMod 47)^(auxiliary-1) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, B_order_47]
  have hd : 23 ∣ spacing := by rw [← spacing_lcm]; exact Nat.dvd_lcm_left _ _
  exact hd.trans spacing_dvd

theorem generator_cast_2011 : (B : ZMod 2011)^(auxiliary-1) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, B_order_2011]
  have hd : 402 ∣ spacing := by rw [← spacing_lcm]; exact Nat.dvd_lcm_right _ _
  exact hd.trans spacing_dvd

theorem generator_cast_fixed : (B : ZMod d)^(auxiliary-1) = 1 := by
  change (B : ZMod (47*2011))^(auxiliary-1) = 1
  apply orderOf_eq_one_iff.mp
  rw [order_product fixed_coprime, generator_cast_47, generator_cast_2011]
  simp

theorem generator_cast_auxiliary : (B : ZMod auxiliary)^(auxiliary-1) = 1 := by
  apply orderOf_eq_one_iff.mp
  have h := generator_order_succ 0
  rw [zero_add, pow_one, pow_zero] at h
  exact h

theorem fixed_auxiliary_coprime : Nat.Coprime d auxiliary := by decide

/-- The fixed factor contributes order1; the entire order comes from p^n. -/
theorem full_order (k : ℕ) :
    orderOf ((B : ZMod (d*auxiliary^(k+1)))^(auxiliary-1)) = auxiliary^k := by
  rw [order_product (fixed_auxiliary_coprime.pow_right (k+1)),
    generator_cast_fixed, generator_order_succ]
  simp

theorem generator_cast_C0 : (B : ZMod (d*auxiliary))^(auxiliary-1) = 1 := by
  apply orderOf_eq_one_iff.mp
  have h := full_order 0
  rw [zero_add, pow_one, pow_zero] at h
  exact h

theorem modulus_factorization (k : ℕ) : (d*auxiliary)*auxiliary^k = d*auxiliary^(k+1) := by
  rw [pow_succ]
  ring

theorem block_order (k : ℕ) :
    orderOf ((B : ZMod ((d*auxiliary)*auxiliary^k))^(auxiliary-1)) = auxiliary^k := by
  rw [modulus_factorization]
  exact full_order k

theorem block_projection (k : ℕ) :
    ZMod.castHom (dvd_mul_right (d*auxiliary) (auxiliary^k)) (ZMod (d*auxiliary))
      ((B : ZMod ((d*auxiliary)*auxiliary^k))^(auxiliary-1)) = 1 := by
  rw [map_pow, map_natCast]
  exact generator_cast_C0

/-- A full coordinate equivalence is constructed for every auxiliary power. -/
theorem exists_coordinates (k : ℕ) :
    ∃ e : ZMod (auxiliary^k) ≃ ZMod (auxiliary^k), ∀ z : ZMod (auxiliary^k),
      ((B : ZMod ((d*auxiliary)*auxiliary^k))^(auxiliary-1))^(e z).val =
        1+((d*auxiliary : ℕ) : ZMod ((d*auxiliary)*auxiliary^k))*
          (z.val : ZMod ((d*auxiliary)*auxiliary^k)) :=
  ControllerPowerCoordinates.exists_power_coordinates (by decide)
    ((B : ZMod ((d*auxiliary)*auxiliary^k))^(auxiliary-1))
    (block_projection k) (block_order k)

/-- The same constructed coordinates, written as powers of the actual B. -/
theorem exists_base_power_coordinates (k : ℕ) :
    ∃ e : ZMod (auxiliary^k) ≃ ZMod (auxiliary^k), ∀ z : ZMod (auxiliary^k),
      (B : ZMod ((d*auxiliary)*auxiliary^k))^((auxiliary-1)*(e z).val) =
        1+((d*auxiliary : ℕ) : ZMod ((d*auxiliary)*auxiliary^k))*
          (z.val : ZMod ((d*auxiliary)*auxiliary^k)) := by
  obtain ⟨e,he⟩ := exists_coordinates k
  exact ⟨e,fun z => by rw [pow_mul]; exact he z⟩

end DiophantineConsistency.CurrentPowerCoordinates2011
