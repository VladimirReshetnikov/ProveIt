import DiophantineConsistency.ArithmeticPellPigeonhole
import DiophantineConsistency.ArithmeticPellStrongDivisibility

/-! Model-internal divisible Pell ordinates above any internal bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellOrdinateAbove
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPigeonhole ArithmeticPellStrongDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_dvd_above (a N L : V) (hN : 0<N) :
    ∃ m : V, L<m ∧ N∣ycoord m a := by
  obtain ⟨j,hj,hdiv⟩ := ordinate_dvd a N hN
  let m:=j*(L+1)
  have hm : L<m := by
    calc
      L<L+1 := lt_add_one L
      _≤j*(L+1) := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hj)
  have hjm : j∣m := ⟨L+1,rfl⟩
  have hy : ycoord j a∣ycoord m a := (y_dvd_iff a j m).mpr hjm
  exact ⟨m,hm,dvd_trans hdiv hy⟩

#print axioms TenPositivePellOrdinateAbove.ordinate_dvd_above
end TenPositivePellOrdinateAbove
