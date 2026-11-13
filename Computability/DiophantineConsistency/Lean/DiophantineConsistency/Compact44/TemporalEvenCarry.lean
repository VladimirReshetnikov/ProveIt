import DiophantineConsistency.Compact44.FractionalTemporalEven
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalEvenCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem carry_one (x c : V) (hc : c≤1) (he : x%2=0) (hp : (1+x+c)%2=0) : c=1 := by
  rcases le_one_iff_eq_zero_or_one.mp hc with hc0 | hc1
  · subst c
    have h : (1+x)%2=1 := by
      rw [mod_add (by norm_num : (0:V)<2),he]
      norm_num
    simp only [add_zero] at hp
    rw [h] at hp
    exact False.elim (_root_.one_ne_zero hp)
  · exact hc1
#print axioms TemporalEvenCarry.carry_one
end TemporalEvenCarry
