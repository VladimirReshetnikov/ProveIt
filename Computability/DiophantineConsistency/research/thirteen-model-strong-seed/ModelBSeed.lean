import DiophantineConsistency.ArithmeticPellPigeonhole

/-! A model-level strong Pell seed with a supplied additional positive
multiplier. This is not a thirteen-variable completeness theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellPigeonhole
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] xcoord ycoord

/-- In every IΣ₁ model a positive-index Pell ordinate is divisible by
`b*c²`; its quotient and abscissa form the strong norm seed. -/
theorem strong_seed_with_multiplier (a b c : V) (hb : 0<b) (hc : 0<c) :
    ∃ t f i : V, 0<t ∧ 0<f ∧ 0<i ∧
      f=xcoord t a ∧ ycoord t a=b*i*c*c ∧
      f*f=1+delta a*(b*i*c*c)*(b*i*c*c) := by
  have hN : 0<b*c*c := mul_pos (mul_pos hb hc) hc
  obtain ⟨t,ht,hd⟩ := ordinate_dvd a (b*c*c) hN
  obtain ⟨i,hi⟩ := hd
  have hy : 0<ycoord t a := lt_of_lt_of_le ht (time_le_y t a)
  have hi' : ycoord t a=b*i*c*c := by
    calc ycoord t a=(b*c*c)*i := hi
      _=b*i*c*c := by ring
  have hi0 : 0<i := by
    apply pos_of_mul_pos_left (b := b*c*c) _ (by simp)
    rw [mul_comm, ←hi]
    exact hy
  have hf : 0<xcoord t a := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x t a)
  refine ⟨t,xcoord t a,i,ht,hf,hi0,rfl,hi',?_⟩
  simpa only [hi'] using norm t a
end ModelBSeed
#print axioms ModelBSeed.strong_seed_with_multiplier
