import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! The auxiliary norm puts the natural graph V below its Pell ordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAuxOrdinateOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Any positive-coefficient auxiliary norm with positive ordinate has
`w ≤ y`; hence `y-w` is an exact natural representative of the difference. -/
theorem ordinate_ge (I w y : V) (hI : 0 < I) (hy : 0 < y)
    (hnorm : I*I*w*w+y*y=1+I*I*y*y) : w≤y := by
  by_contra h
  have hyw : y+1≤w := lt_iff_succ_le.mp (lt_of_not_ge h)
  have hsq : (y+1)*(y+1)≤w*w := mul_le_mul hyw hyw (by simp) (by simp)
  have hsq' : y*y+1≤w*w := by
    calc y*y+1 ≤ y*y+1+(y+y) := le_add_of_nonneg_right (by simp)
         _ = (y+1)*(y+1) := by ring
         _ ≤ w*w := hsq
  have hm : I*I*y*y+I*I ≤ I*I*w*w := by
    have ht := mul_le_mul_of_nonneg_left hsq' (show (0:V)≤I*I by simp)
    calc I*I*y*y+I*I=I*I*(y*y+1) := by ring
         _ ≤ I*I*(w*w) := ht
         _ = I*I*w*w := by ring
  have hQ : 0 < I*I := mul_pos hI hI
  have hy2 : 0 < y*y := mul_pos hy hy
  have hle : I*I*y*y+1 ≤ I*I*w*w := by
    have h1 : I*I*y*y+1 ≤ I*I*y*y+I*I := by
      simpa only [add_comm] using add_le_add_left (pos_iff_one_le.mp hQ) (I*I*y*y)
    exact le_trans h1 hm
  have hlt : I*I*y*y+1 < I*I*w*w+y*y :=
    lt_of_le_of_lt hle (lt_add_of_pos_right _ hy2)
  have heq : I*I*w*w+y*y=I*I*y*y+1 := by rw [hnorm]; ring
  rw [heq] at hlt
  exact (Arithmetic.lt_irrefl _) hlt

#print axioms CompactAuxOrdinateOrder.ordinate_ge
end CompactAuxOrdinateOrder
