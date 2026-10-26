import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! Exact arithmetic comparison fixture.  The controller's radix, B, auxiliary,
    dimension and the used source data facts are retained.  No theorem is assumed.
    This checks the three replaced proofs, not production clients or the full K dependency. -/
namespace ProofSimplification.ControllerPowerComparison
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace CurrentMasks2011
def width : ℕ := 94517
def radix : ℕ := 2^47
end CurrentMasks2011
def d : ℕ := CurrentMasks2011.width
def B : ℕ := CurrentMasks2011.radix^2011
def auxiliary : ℕ := 120199
def dimension (n : ℕ) : ℕ := auxiliary^n
instance : NeZero auxiliary := ⟨by decide⟩
theorem B_eq : B = 2^94517 := by
  unfold B CurrentMasks2011.radix
  rw [← pow_mul]

theorem prime_auxiliary : Nat.Prime auxiliary := by norm_num [auxiliary]

theorem order_coprime_47 : Nat.Coprime 23 d := by decide

theorem order_coprime_2011 : Nat.Coprime 402 d := by decide

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

attribute [local irreducible] B

theorem auxiliary_modEq_23 : auxiliary ≡ 1 [MOD 23] := by decide
theorem auxiliary_modEq_402 : auxiliary ≡ 1 [MOD 402] := by decide

namespace Before
/-- Exact power reduction at the first fixed prime, for every exponent. -/
theorem power_dimension_47 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 47) = (B : ZMod 47) := by
  have he : dimension n ≡ 1 [MOD 23] := by
    simpa only [dimension, one_pow] using auxiliary_modEq_23.pow n
  have hp : (B : ZMod 47)^23 = 1 := by
    rw [← B_order_47]
    exact pow_orderOf_eq_one _
  simpa only [Nat.cast_pow, pow_one] using pow_eq_pow_of_modEq he hp

/-- The second fixed-prime order is 402, not 2010. -/
theorem power_dimension_2011 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 2011) = (B : ZMod 2011) := by
  have he : dimension n ≡ 1 [MOD 402] := by
    simpa only [dimension, one_pow] using auxiliary_modEq_402.pow n
  have hp : (B : ZMod 2011)^402 = 1 := by
    rw [← B_order_2011]
    exact pow_orderOf_eq_one _
  simpa only [Nat.cast_pow, pow_one] using pow_eq_pow_of_modEq he hp

/-- Frobenius handles all auxiliary powers, including auxiliary^0 = 1. -/
theorem power_dimension_auxiliary (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod auxiliary) = (B : ZMod auxiliary) := by
  letI : Fact auxiliary.Prime := ⟨prime_auxiliary⟩
  simpa only [dimension, Nat.cast_pow] using
    (ZMod.pow_card_pow (n := n) (B : ZMod auxiliary))


#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary
end Before

namespace After
/-- A fixed point of one power map stays fixed under every iterate, including zero. -/
private theorem pow_pow_fixed {M : Type*} [Monoid M] (x : M) (a n : ℕ)
    (h : x^a=x) : x^(a^n)=x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_mul,ih,h]

/-- The first literal residue is fixed by raising to the auxiliary power. -/
theorem power_dimension_47 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 47) = (B : ZMod 47) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod 47) auxiliary n (by rw [B_cast_47]; unfold auxiliary; reduce_mod_char)

theorem power_dimension_2011 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 2011) = (B : ZMod 2011) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod 2011) auxiliary n (by rw [B_cast_2011]; unfold auxiliary; reduce_mod_char)

theorem power_dimension_auxiliary (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod auxiliary) = (B : ZMod auxiliary) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod auxiliary) auxiliary n (by rw [B_cast_auxiliary]; unfold auxiliary; reduce_mod_char)


#print axioms pow_pow_fixed
#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary

-- The zero exponent is explicitly supported by the public conclusions.
example : ((B^(dimension 0) : ℕ) : ZMod 47) = B := power_dimension_47 0
example : ((B^(dimension 0) : ℕ) : ZMod 2011) = B := power_dimension_2011 0
example : ((B^(dimension 0) : ℕ) : ZMod auxiliary) = B := power_dimension_auxiliary 0
end After
end ProofSimplification.ControllerPowerComparison
