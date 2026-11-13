import DiophantineConsistency.Compact44.CompactSymbolicKernel
import DiophantineConsistency.ArithmeticStandardCasts
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelCast
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (((∑ i ∈ s, f i):ℕ):V) = ∑ i ∈ s, (f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

theorem cast_reflected_sum {ι : Type*} [Fintype ι] (r : ℕ) (e c : ι → ℕ) (u v : ℕ) :
    (((∑ i, c i*(r^(u-e i)+r^(v-e i))):ℕ):V) =
      ∑ i, (c i:V)*((r:V)^(u-e i)+(r:V)^(v-e i)) := by
  rw [cast_sum_generic]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
#print axioms CompactSymbolicKernelCast.cast_reflected_sum
end CompactSymbolicKernelCast
