import DiophantineConsistency.CurrentKernel2011
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-!
# Exact finite controller data at the maintained 2011-cell ports

The prime, order, spacing, base-residue and auxiliary-lift facts below
are kernel-checked. The actual K-residue hypotheses in the final three
Hs wrappers are explicit pending a separate literal modular-kernel
evaluation. This module does not claim a complete Pcst discharge.
-/

namespace DiophantineConsistency.CurrentControllerData2011

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def d : ℕ := CurrentMasks2011.width
def B : ℕ := CurrentMasks2011.radix ^ 2011
def auxiliary : ℕ := 120199
def spacing : ℕ := 9246

instance : NeZero auxiliary := ⟨by decide⟩
instance : NeZero (auxiliary^2) := ⟨by decide⟩

theorem d_eq : d = 94517 := rfl
theorem d_factors : d = 47*2011 := rfl
theorem B_eq : B = 2^94517 := by
  unfold B CurrentMasks2011.radix
  rw [← pow_mul]

theorem prime_47 : Nat.Prime 47 := by norm_num
theorem prime_2011 : Nat.Prime 2011 := by norm_num
theorem prime_auxiliary : Nat.Prime auxiliary := by norm_num [auxiliary]
theorem fixed_distinct : (47 : ℕ) ≠ 2011 := by decide
theorem fixed_coprime : Nat.Coprime 47 2011 := by decide
theorem d_odd : Odd d := by decide
theorem d_squarefree : Squarefree d := by
  rw [d_factors,Nat.squarefree_mul fixed_coprime]
  exact ⟨prime_47.squarefree,prime_2011.squarefree⟩

theorem auxiliary_gt_d : d < auxiliary := by decide
theorem auxiliary_odd : Odd auxiliary := by decide
theorem spacing_factorization : spacing = 23*402 ∧ 402 = 2*3*67 := by decide
theorem spacing_lcm : Nat.lcm 23 402 = spacing := by decide
theorem auxiliary_progression : auxiliary = 13*spacing+1 := by decide
theorem spacing_dvd : spacing ∣ auxiliary-1 := by decide
theorem order_coprime_47 : Nat.Coprime 23 d := by decide
theorem order_coprime_2011 : Nat.Coprime 402 d := by decide
theorem spacing_coprime : Nat.Coprime spacing d := by decide

theorem two_pow_47 : (2 : ZMod 47)^23 = 1 := by reduce_mod_char
theorem two_pow_2011 : (2 : ZMod 2011)^402 = 1 := by reduce_mod_char
theorem proper_power_2011_2 : (2 : ZMod 2011)^201 = 2010 := by reduce_mod_char
theorem proper_power_2011_3 : (2 : ZMod 2011)^134 = 205 := by reduce_mod_char
theorem proper_power_2011_67 : (2 : ZMod 2011)^6 = 64 := by reduce_mod_char

theorem two_order_47 : orderOf (2 : ZMod 47) = 23 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) two_pow_47
  intro p hp hd
  have he : p = 23 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
  subst p
  reduce_mod_char
  decide

theorem two_order_2011 : orderOf (2 : ZMod 2011) = 402 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) two_pow_2011
  intro p hp hd
  have hd' : p ∣ 2*3*67 := hd
  have he : p = 2 ∨ p = 3 ∨ p = 67 := by
    rcases hp.dvd_mul.mp hd' with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  rcases he with rfl | rfl | rfl <;> reduce_mod_char <;> decide

theorem B_order_47 : orderOf (B : ZMod 47) = 23 := by
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat]
  have h : Nat.Coprime (orderOf (2 : ZMod 47)) 94517 := by
    rw [two_order_47]
    exact order_coprime_47
  rw [h.orderOf_pow,two_order_47]

theorem B_order_2011 : orderOf (B : ZMod 2011) = 402 := by
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat]
  have h : Nat.Coprime (orderOf (2 : ZMod 2011)) 94517 := by
    rw [two_order_2011]
    exact order_coprime_2011
  rw [h.orderOf_pow,two_order_2011]

theorem B_cast_47 : (B : ZMod 47) = 37 := by
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat]
  reduce_mod_char

theorem B_cast_2011 : (B : ZMod 2011) = 1283 := by
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat]
  reduce_mod_char

theorem B_cast_auxiliary : (B : ZMod auxiliary) = 37435 := by
  unfold auxiliary
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat]
  reduce_mod_char

private theorem mod_of_cast {m : ℕ} [NeZero m] (a b : ℕ)
    (h : (a : ZMod m) = (b : ZMod m)) (hb : b < m) : a % m = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hb] using hv

theorem B_mod_47 : B % 47 = 37 := mod_of_cast B 37 B_cast_47 (by decide)
theorem B_mod_2011 : B % 2011 = 1283 := mod_of_cast B 1283 B_cast_2011 (by decide)
theorem B_mod_auxiliary : B % auxiliary = 37435 :=
  mod_of_cast B 37435 B_cast_auxiliary (by decide)

theorem B_square_mod_47 : B^2 % 47 = 6 := by rw [Nat.pow_mod,B_mod_47]
theorem B_square_mod_2011 : B^2 % 2011 = 1091 := by rw [Nat.pow_mod,B_mod_2011]
theorem B_square_mod_auxiliary : B^2 % auxiliary = 99283 := by
  rw [Nat.pow_mod,B_mod_auxiliary]
  decide

/-- Modular exponentiation checks the complete 11360754366 exponent;
the unreduced natural power is never materialized. -/
theorem auxiliary_lift_cast :
    (B : ZMod (auxiliary^2))^(auxiliary-1) = 7300767062 := by
  unfold auxiliary
  rw [B_eq,Nat.cast_pow,Nat.cast_ofNat,← pow_mul]
  change (2 : ZMod 14447799601)^11360754366 = 7300767062
  reduce_mod_char

theorem auxiliary_lift : B^(auxiliary-1) % auxiliary^2 = 7300767062 := by
  apply mod_of_cast (B^(auxiliary-1)) 7300767062
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using auxiliary_lift_cast
  · decide

theorem lift_nonzero_digit :
    7300767062 = 1+auxiliary*60739 ∧ 0 < (60739 : ℕ) ∧ 60739 < auxiliary := by decide

theorem auxiliary_square_ne_one : B^2 % auxiliary ≠ 1 := by
  rw [B_square_mod_auxiliary]
  decide

theorem lift_ne_one : B^(auxiliary-1) % auxiliary^2 ≠ 1 := by
  rw [auxiliary_lift]
  decide

/- These final arithmetic wrappers explicitly require the still-separate
actual kernel residues. They do not discharge those finite premises. -/
-- This interface uses K symbolically; it must not evaluate the literal
-- 942-row physical permutation while checking elementary modular algebra.
attribute [local irreducible] CurrentKernel2011.K B

theorem Hs_mod_47 (hK : CurrentKernel2011.K % 47 = 26) : (1+B*CurrentKernel2011.K+B^2) % 47 = 29 := by
  rw [Nat.add_mod (1+B*CurrentKernel2011.K),Nat.add_mod 1,
    Nat.mul_mod B CurrentKernel2011.K,B_mod_47,hK,B_square_mod_47]

theorem Hs_mod_2011 (hK : CurrentKernel2011.K % 2011 = 1995) : (1+B*CurrentKernel2011.K+B^2) % 2011 = 674 := by
  rw [Nat.add_mod (1+B*CurrentKernel2011.K),Nat.add_mod 1,
    Nat.mul_mod B CurrentKernel2011.K,B_mod_2011,hK,B_square_mod_2011]

theorem Hs_mod_auxiliary (hK : CurrentKernel2011.K % auxiliary = 114787) :
    (1+B*CurrentKernel2011.K+B^2) % auxiliary = 36379 := by
  rw [Nat.add_mod (1+B*CurrentKernel2011.K),Nat.add_mod 1,
    Nat.mul_mod B CurrentKernel2011.K,B_mod_auxiliary,hK,B_square_mod_auxiliary]; decide

end DiophantineConsistency.CurrentControllerData2011
