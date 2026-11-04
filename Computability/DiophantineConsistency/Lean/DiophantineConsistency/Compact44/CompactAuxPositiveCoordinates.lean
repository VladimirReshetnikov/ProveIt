import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! Positive ordinary-tail coordinates from an auxiliary Pell seed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAuxPositiveCoordinates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellAuxiliarySeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive rank makes the auxiliary ordinate, Pell x-coordinate and
shifted positive graph coordinate `f-1` positive. -/
theorem auxiliary_f_pos (a R c f : V) (hR : 0<R)
    (hc : c=ycoord R a) (hf : f=xcoord (R*c) a) :
    0<c ∧ 1<f ∧ 0<f-1 ∧ (f-1)+1=f := by
  have hcpos : 0<c := by
    rw [hc]
    exact lt_of_lt_of_le hR (time_le_y R a)
  have hp : 0<R*c := mul_pos hR hcpos
  have hone : 1<f := by
    rw [hf]
    exact lt_of_le_of_lt (le_trans (pos_iff_one_le.mp hp) (time_le_y (R*c) a))
      (ordinate_lt_abscissa a (R*c))
  exact ⟨hcpos,hone,tsub_pos_of_lt hone,tsub_add_cancel_of_le hone.le⟩

/-- The ordinary multiplier is Δ times the normalized seed multiplier. Its
square identity and both displayed coordinates follow in every model. -/
theorem ordinary_coordinates (a R c f i w : V) (hR : 0<R)
    (hc : c=ycoord R a) (hf : f=xcoord (R*c) a)
    (hi : 0<i) (hw : 0<w)
    (hn : f*f=1+delta a*(i*c*c)*(i*c*c)) :
    0<f-1 ∧ (f-1)+1=f ∧ 0<delta a*i ∧ 0<delta a*i+w ∧
      delta a*(f*f-1) = (c*c*c*c)*(delta a*i)*(delta a*i) := by
  obtain ⟨_,_,ht,he⟩ := auxiliary_f_pos a R c f hR hc hf
  have hnsub : f*f-1=delta a*(i*c*c)*(i*c*c) := by rw [hn, add_comm, add_tsub_cancel_right]
  have hd : 0<delta a := by unfold delta; exact mul_pos (by simp) (by simp)
  refine ⟨ht,he,mul_pos hd hi,?_,?_⟩
  · exact lt_of_lt_of_le hw (le_add_of_nonneg_left (by simp))
  · rw [hnsub]; ring

#print axioms CompactAuxPositiveCoordinates.auxiliary_f_pos
#print axioms CompactAuxPositiveCoordinates.ordinary_coordinates
end CompactAuxPositiveCoordinates
