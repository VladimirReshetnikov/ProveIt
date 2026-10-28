import DiophantineConsistency.ArithmeticPellStrongDivisibility

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellStrongDivisibilityChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization ArithmeticPellStrongDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (b m n : V) :
    gcdValue (ycoord m b) (ycoord n b)=ycoord (gcdValue m n) b :=
  strong_divisibility b m n

/-- Index zero is included, with no modulo-zero interpretation. -/
example (b n : V) : ycoord 0 b∣ycoord n b ↔ n=0 := by
  rw [y_dvd_iff]
  simp

example (b m : V) : ycoord m b∣ycoord 0 b := (y_dvd_iff b m 0).mpr (dvd_zero m)

example (b n : V) : ycoord 1 b∣ycoord n b := (y_dvd_iff b 1 n).mpr (one_dvd n)

example (b m : V) : gcdValue (ycoord m b) (ycoord m b)=ycoord m b :=
  gcd_left_of_dvd _ _ (dvd_refl _)

/-- The norm certificate explicitly covers a zero divisor when permitted. -/
example (b : V) : Bez (xcoord 0 b) 0 1 :=
  norm_unit_certificate b 0 0 (by simp)

example (T : V) : gcdValue (T*0) (T*0)=T*gcdValue 0 0 := gcd_scale T 0 0

example (b m n T h : V) (hm : h∣T*ycoord m b) (hn : h∣T*ycoord n b) :
    h∣T*ycoord (gcdValue m n) b := scaled_common_divisor b m n T h hm hn

example (b m n h : V) : h∣0*ycoord (gcdValue m n) b :=
  scaled_common_divisor b m n 0 h (by simp) (by simp)

#print axioms norm_unit_certificate
#print axioms common_divisors_add
#print axioms strong_divisibility
#print axioms y_strictMono
#print axioms y_dvd_iff
#print axioms gcd_scale
#print axioms scaled_common_divisor
end DiophantineConsistency.ArithmeticPellStrongDivisibilityChecks
