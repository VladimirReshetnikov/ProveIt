import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace AdaptiveModFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exists_residue (x : V) : ∃ n : ℕ, x % 4 = (n : V) := by
  apply eq_nat_of_lt_nat
  simpa using (mod_lt x (b := (4:V)) (by simp))

private def residueNat (x : V) : ℕ := Classical.choose (exists_residue x)
private theorem residueNat_eq (x : V) : (residueNat x : V) = x % 4 :=
  (Classical.choose_spec (exists_residue x)).symm
private theorem residueNat_lt (x : V) : residueNat x < 4 := by
  have h : (residueNat x : V) < 4 := by rw [residueNat_eq]; exact mod_lt x (by simp)
  exact_mod_cast h

def residue (x : V) : ZMod 4 := residueNat x

theorem residue_equal {x y : V} (h : x%4 = y%4) : residue x = residue y := by
  have he : (residueNat x : V) = (residueNat y : V) := by rw [residueNat_eq,residueNat_eq,h]
  have hn : residueNat x = residueNat y := Nat.cast_inj.mp he
  simp only [residue,hn]

theorem cast_mod (n : ℕ) : (((n % 4):ℕ) : V) = (n : V)%4 := by
  have hn : (n : V) = ((n%4:ℕ):V)+4*((n/4:ℕ):V) := by
    have h := Nat.mod_add_div n 4
    exact_mod_cast h.symm
  rw [hn, mod_add_mul' _ _ (by simp : (0:V)<4)]
  symm
  apply mod_eq_self_of_lt
  exact_mod_cast (Nat.mod_lt n (by decide : 0<4))

theorem residue_nat (n : ℕ) : residue (n : V) = (n : ZMod 4) := by
  have he : (residueNat (n:V) : V) = ((n%4:ℕ):V) := by rw [residueNat_eq, cast_mod]
  have hn : residueNat (n:V) = n%4 := Nat.cast_inj.mp he
  simp only [residue,hn,ZMod.natCast_mod]

theorem residue_add (a b : V) : residue (a+b) = residue a + residue b := by
  have h : (a+b)%4 = (((residueNat a + residueNat b):ℕ):V)%4 := by
    rw [mod_add (by simp : (0:V)<4),Nat.cast_add,residueNat_eq,residueNat_eq]
  calc
    residue (a+b) = residue (((residueNat a + residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a + residueNat b):ℕ) := residue_nat _
    _ = residue a + residue b := by simp only [residue, Nat.cast_add]

theorem residue_mul (a b : V) : residue (a*b) = residue a * residue b := by
  have h : (a*b)%4 = (((residueNat a * residueNat b):ℕ):V)%4 := by
    rw [mod_mul (by simp : (0:V)<4),Nat.cast_mul,residueNat_eq,residueNat_eq]
  calc
    residue (a*b) = residue (((residueNat a * residueNat b):ℕ):V) := residue_equal h
    _ = ((residueNat a * residueNat b):ℕ) := residue_nat _
    _ = residue a * residue b := by simp only [residue, Nat.cast_mul]
end AdaptiveModFour
