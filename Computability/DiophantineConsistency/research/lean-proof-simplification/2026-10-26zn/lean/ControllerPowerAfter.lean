import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

namespace ProofSimplification.ControllerPowerAfter
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
end ProofSimplification.ControllerPowerAfter
