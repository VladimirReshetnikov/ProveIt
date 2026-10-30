import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionPositive2011

/-! The first-Pell seed dominates the old scaled ordinate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionSeedSize2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual first-index seed hypotheses imply the size premise used by
positive first-carrier construction, uniformly in every model. -/
theorem seed_ordinate_le_k (q X Y sY k time : V)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y)
    (hYq : Y=sY*q^3) (ht : 2≤time)
    (hk : k=2*ycoord time (2*(X*Y*Y-1)+1)) : sY≤k := by
  let Q := X*Y*Y
  let b := 2*(Q-1)+1
  have hQ : (1:V)≤Q := one_le_mul (one_le_mul (pos_iff_one_le.mp hX) (pos_iff_one_le.mp hY)) (pos_iff_one_le.mp hY)
  have hsub : Q-1+1=Q := tsub_add_cancel_of_le hQ
  have hb : b+1=2*Q := by
    dsimp only [b]
    calc _=2*(Q-1+1) := by ring
         _=2*Q := by rw [hsub]
  have hy2 : ycoord (2:V) b=2*(b+2) := by
    rw [show (2:V)=0+1+1 by norm_num, y_succ, x_succ, y_succ]
    simp
    ring
  have hytime : ycoord (2:V) b≤ycoord time b := by
    have hr : 2+(time-2)=time := add_tsub_cancel_of_le ht
    have h := ordinate_add_ge (2:V) (time-2) b
    rw [hr] at h
    exact le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (time-2))) h
  have hqpow : (1:V)≤q^3 := pos_iff_one_le.mp (pow_pos hq _)
  have hsY : sY≤Y := by
    rw [hYq]
    exact le_mul_of_one_le_right (Arithmetic.zero_le sY) hqpow
  have hYQ : Y≤Q := by
    dsimp only [Q]
    exact le_mul_of_one_le_left (Arithmetic.zero_le Y)
      (one_le_mul (pos_iff_one_le.mp hX) (pos_iff_one_le.mp hY))
  have hQb : Q≤b+2 := by
    calc Q ≤ 2*Q := le_mul_of_one_le_left (Arithmetic.zero_le Q) (by norm_num : (1:V)≤2)
         _ = b+1 := hb.symm
         _ ≤ b+2 := by simpa only [show (2:V)=1+1 by norm_num, ← add_assoc] using
           le_add_of_nonneg_right (show (0:V)≤1 by simp)
  have hbY : b+2≤ycoord time b := by
    calc b+2 ≤ 2*(b+2) := le_mul_of_one_le_left (by simp) (by norm_num : (1:V)≤2)
         _ = ycoord 2 b := hy2.symm
         _ ≤ ycoord time b := hytime
  calc sY ≤ Y := hsY
       _ ≤ Q := hYQ
       _ ≤ b+2 := hQb
       _ ≤ ycoord time b := hbY
       _ ≤ 2*ycoord time b := le_mul_of_one_le_left (by simp) (by norm_num : (1:V)≤2)
       _ = k := hk.symm
end DiophantineConsistency.ArithmeticAdaptiveConstructionSeedSize2011
