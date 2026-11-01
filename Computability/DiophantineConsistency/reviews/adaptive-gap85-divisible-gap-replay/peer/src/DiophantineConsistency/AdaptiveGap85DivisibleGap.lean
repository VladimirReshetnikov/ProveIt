import DiophantineConsistency.AdaptiveGap85ActualAllIndicesRoot
set_option autoImplicit false
/-! A conditional residue obstruction to the reverse gap, not a zero-existence claim. -/
namespace DiophantineConsistency.AdaptiveGap85DivisibleGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem divisible_blocks (b F C : V) (hF : 0<F) (hC : 0<C) (h : b∣F) : ¬ F+C<1+b := by
  have hbF : b≤F := Arithmetic.le_of_dvd hF h
  have hC1 : 1≤C := pos_iff_one_le.mp hC
  apply not_lt_of_ge
  calc
    1+b = b+1 := by ac_rfl
    _ ≤ F+C := add_le_add hbF hC1
theorem forward_preserves (b F t : V) (h : b∣F) : b∣F+b*t :=
  dvd_add h (dvd_mul_right b t)

end DiophantineConsistency.AdaptiveGap85DivisibleGap
