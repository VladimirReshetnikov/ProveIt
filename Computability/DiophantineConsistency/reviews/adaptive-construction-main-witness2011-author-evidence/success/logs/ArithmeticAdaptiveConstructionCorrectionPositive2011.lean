import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrection2011

/-! The seed correction is large enough to absorb the deleted multiplier.
The seed index and divisibility relations remain explicit hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionPositive2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem time_lt_ordinate (time b : V) (ht : 2≤time) : time<ycoord time b := by
  have h2 : (2:V)<ycoord 2 b := by
    have he : ycoord (2:V) b = 2*(b+2) := by
      rw [show (2:V)=0+1+1 by norm_num, y_succ, x_succ, y_succ]
      simp
      ring
    rw [he]
    have hb : (2:V) ≤ b+2 := le_add_of_nonneg_left (Arithmetic.zero_le b)
    have hm : (4:V) ≤ 2*(b+2) := by
      simpa only [show (2:V)*2=4 by norm_num] using mul_le_mul_of_nonneg_left hb (by simp : (0:V)≤2)
    exact lt_of_lt_of_le (by norm_num) hm
  have hr : 2+(time-2)=time := add_tsub_cancel_of_le ht
  have h := ordinate_add_ge (2:V) (time-2) b
  rw [hr] at h
  calc time = 2+(time-2) := hr.symm
       _ < ycoord 2 b+(time-2) := by simpa only [add_comm] using add_lt_add_right h2 (time-2)
       _ ≤ ycoord time b := h

/-- If the chosen index is at least two, the quotient supplies a strictly
positive adaptive correction even after subtracting the deleted multiplier. -/
theorem positive_main_correction (q X Y sY R k time w gammaOld : V)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hsY : 0<sY) (hg : 0<gammaOld)
    (hYq : Y=sY*q^3) (hXq : X=q*w) (ht : 2≤time)
    (hR : R+1=2*time)
    (hk : k=2*ycoord time (2*(X*Y*Y-1)+1)) :
    ∃ t gamma : V, 0<gamma ∧ k=R+1+(Y*q^2)*t ∧ gamma+w=gammaOld+t := by
  let Q := X*Y*Y
  let b := 2*(Q-1)+1
  have hQ : (1:V)≤Q := pos_iff_one_le.mp (mul_pos (mul_pos hX hY) hY)
  have hsub : Q-1+1=Q := tsub_add_cancel_of_le hQ
  have hb : b+1=2*Q := by
    dsimp only [b]
    calc _=2*(Q-1+1) := by ring
         _=2*Q := by rw [hsub]
  have hm : 2*Q ∣ b+1 := ⟨1, by simpa only [mul_one] using hb⟩
  obtain ⟨_,s,_,hy⟩ := residue_quotients time b (2*Q) hm
  have hs : 0<s := by
    by_contra hn
    have hz : s=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hz,mul_zero,add_zero] at hy
    exact (ne_of_gt (time_lt_ordinate time b ht)) hy
  let t := 4*X*(sY*q)*s
  have hke : k=R+1+(Y*q^2)*t := by
    rw [hk]
    change 2*ycoord time b = R+1+(Y*q^2)*t
    rw [hy,hR]
    dsimp only [t,Q]
    rw [hYq]
    ring
  have hwX : w≤X := by
    rw [hXq]
    exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hq)
  have htX : X≤t := by
    have hsq : (1:V)≤sY*q := one_le_mul (pos_iff_one_le.mp hsY) (pos_iff_one_le.mp hq)
    have hs1 : (1:V)≤s := pos_iff_one_le.mp hs
    dsimp only [t]
    calc X ≤ 4*X := le_mul_of_one_le_left (Arithmetic.zero_le X) (by norm_num : (1:V)≤4)
         _ ≤ (4*X)*(sY*q) := le_mul_of_one_le_right (by simp) hsq
         _ ≤ (4*X)*(sY*q)*s := le_mul_of_one_le_right (by simp) hs1
  have hgt : w<gammaOld+t := by
    calc w ≤ t := le_trans hwX htX
         _ < t+gammaOld := lt_add_of_pos_right t hg
         _ = gammaOld+t := by ring
  refine ⟨t,gammaOld+t-w,tsub_pos_iff_lt.mpr hgt,hke,?_⟩
  exact tsub_add_cancel_of_le (le_of_lt hgt)
end DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionPositive2011
