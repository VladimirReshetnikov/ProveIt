import DiophantineConsistency.ArithmeticPellRecurrence

/-! A local compatibility lemma for providers whose Pell recurrence object
predates the corresponding theorem in the current source. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellOrdinateCompat
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_add_ge (left right b : V) : ycoord left b + right ≤ ycoord (left + right) b := by
  rw [(addition left right b).2]
  calc
    ycoord left b + right ≤ ycoord left b * xcoord right b + xcoord left b * ycoord right b :=
      _root_.add_le_add (le_mul_of_one_le_right (Arithmetic.zero_le _) (one_le_x right b))
        (le_trans (time_le_y right b) (le_mul_of_one_le_left (Arithmetic.zero_le _) (one_le_x left b)))
    _ = _ := add_comm _ _
end DiophantineConsistency.ArithmeticPellOrdinateCompat
