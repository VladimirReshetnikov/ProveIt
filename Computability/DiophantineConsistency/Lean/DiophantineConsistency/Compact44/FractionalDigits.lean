import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FractionalDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A fractional radix digit from adjacent complete radix digits. -/
theorem split_quotient (Y d t : V) (hd : 0<d) (ht : 0<t) :
    (Y / d) % (d*t) = (Y % (d*t)) / d + (Y / (d*t) % d) * t := by
  have hr := mod_mul_split Y d (d*t) hd (mul_pos hd ht)
  have hs := mod_mul_split Y (d*t) d (mul_pos hd ht) hd
  have hh : (Y % (d*(d*t))) / d = (Y/d) % (d*t) := by
    rw [hr, add_comm, div_mul_add _ _ (mod_lt Y hd)]
  rw [show d*(d*t)=(d*t)*d by ring, hs] at hh
  have hh2 : Y % (d*t) + Y / (d*t) % d * (d*t) =
      Y % (d*t) + (Y / (d*t) % d * t)*d := by ring
  rw [hh2, div_add_mul_self _ _ hd] at hh
  exact hh.symm
#print axioms FractionalDigits.split_quotient
end FractionalDigits
