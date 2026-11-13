import DiophantineConsistency.CompactCoefficientMass
import DiophantineConsistency.ArithmeticWindowCarry
import DiophantineConsistency.ArithmeticStandardCasts
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactModelStencilSlack
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fixed finite stencil mass leaves more than half a radix of slack. -/
theorem stencil_below_half :
    3*(CompactCoefficientMass.stencilMass:V)+1 < Exp.exp 66 := by
  have hnat := CompactCoefficientMass.triple_stencil_below_half
  have hm : 3*(CompactCoefficientMass.stencilMass:V)+1 < ((2^66:ℕ):V) := by
    exact_mod_cast hnat
  have he : ((2^66:ℕ):V)=Exp.exp (66:V) := by
    simpa using (DiophantineConsistency.ArithmeticStandardCasts.cast_exp (V:=V) 66).symm
  rwa [he] at hm

/-- Conservative mass plus one arbitrary radix digit fits the b=1 carry bound. -/
theorem stencil_mass_b1 :
    3*(CompactCoefficientMass.stencilMass:V)+(Exp.exp 67-1)+1 ≤
      ((1:V)+1)*(Exp.exp 67-1) := by
  have hn : 3*CompactCoefficientMass.stencilMass+2 ≤ 2^67 := by
    rw [CompactCoefficientMass.stencil_mass_exact]
    decide
  have hm : 3*(CompactCoefficientMass.stencilMass:V)+2 ≤ ((2^67:ℕ):V) := by
    exact_mod_cast hn
  have he : ((2^67:ℕ):V)=Exp.exp (67:V) := by
    simpa using (DiophantineConsistency.ArithmeticStandardCasts.cast_exp (V:=V) 67).symm
  rw [he] at hm
  have hr : Exp.exp (67:V)-1+1=Exp.exp 67 := tsub_add_cancel_of_le (one_le_exp _)
  have hsmall : 3*(CompactCoefficientMass.stencilMass:V)+1 ≤ Exp.exp 67-1 := by
    apply (add_le_add_iff_right 1).mp
    calc
      (3*(CompactCoefficientMass.stencilMass:V)+1)+1 = 3*(CompactCoefficientMass.stencilMass:V)+2 := by ring
      _ ≤ Exp.exp 67 := hm
      _ = (Exp.exp 67-1)+1 := hr.symm
  calc
    3*(CompactCoefficientMass.stencilMass:V)+(Exp.exp 67-1)+1 =
        (3*(CompactCoefficientMass.stencilMass:V)+1)+(Exp.exp 67-1) := by ring
    _ ≤ (Exp.exp 67-1)+(Exp.exp 67-1) := add_le_add_right hsmall _
    _ = ((1:V)+1)*(Exp.exp 67-1) := by ring

/-- The actual family-to-stencil mass bound is an explicit separate premise. -/
theorem family_mass_b1 {ι : Type*} [Fintype ι] (a : ι → V)
    (hcoeff : (∑ i,a i) ≤ (CompactCoefficientMass.stencilMass:V)) :
    ((∑ i,a i*3)+(Exp.exp 67-1))+1 ≤ ((1:V)+1)*(Exp.exp 67-1) := by
  have h3 : (∑ i,a i*3) ≤ 3*(CompactCoefficientMass.stencilMass:V) := by
    rw [←Finset.sum_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcoeff (by simp : (0:V)≤3)
  calc
    ((∑ i,a i*3)+(Exp.exp 67-1))+1 ≤
        (3*(CompactCoefficientMass.stencilMass:V)+(Exp.exp 67-1))+1 :=
      add_le_add_right (add_le_add_right h3 _) _
    _ ≤ ((1:V)+1)*(Exp.exp 67-1) := stencil_mass_b1

#print axioms CompactModelStencilSlack.stencil_below_half
#print axioms CompactModelStencilSlack.stencil_mass_b1
#print axioms CompactModelStencilSlack.family_mass_b1
end CompactModelStencilSlack
