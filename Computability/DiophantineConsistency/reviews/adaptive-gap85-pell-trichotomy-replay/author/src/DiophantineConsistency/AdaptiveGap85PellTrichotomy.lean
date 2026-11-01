import DiophantineConsistency.ArithmeticPellFirstNorm

/-! First-norm Pell index trichotomy in arbitrary IΣ₁ models. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PellTrichotomy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_norm_trichotomy (q x k : V) (hk : 0<k)
    (hn : x*x=1+discriminant q*k*k) :
    k=2 ∨ k=8*(q+1)+4 ∨ 32*(q+1)*(q+1)+32*(q+1)+6 ≤ k := by
  obtain ⟨time,ht,_,_,hkval⟩ := positive_solution_index q x k hk hn
  let b : V := 2*q+1
  have hy1 : ycoord 1 b=1 := by
    simpa only [zero_add,x_zero,y_zero,mul_zero,add_zero] using (y_succ (0:V) b)
  have hx1 : xcoord 1 b=b+2 := by
    simpa only [zero_add,x_zero,y_zero,mul_zero,add_zero,mul_one] using (x_succ (0:V) b)
  have hy2 : ycoord 2 b=2*(b+2) := by
    have h := y_succ (1:V) b
    rw [hy1,hx1] at h
    simpa only [one_add_one_eq_two] using h.trans (by ring)
  have hx2 : xcoord 2 b=(b+2)*(b+2)+delta b := by
    have h := x_succ (1:V) b
    rw [hy1,hx1,mul_one] at h
    simpa only [one_add_one_eq_two] using h
  have hy3 : ycoord 3 b=16*(q+1)*(q+1)+16*(q+1)+3 := by
    have h := y_succ (2:V) b
    rw [hy2,hx2] at h
    calc
      ycoord 3 b = (b+2)*(b+2)+delta b+(b+2)*(2*(b+2)) := by
        simpa only [show (2:V)+1=3 by ring] using h
      _ = 16*(q+1)*(q+1)+16*(q+1)+3 := by dsimp [b,delta]; ring
  by_cases h1 : time=1
  · left
    rw [h1] at hkval
    change 2*ycoord 1 b=k at hkval
    rw [hy1,mul_one] at hkval
    exact hkval.symm
  · by_cases h2 : time=2
    · right; left
      rw [h2,hy2] at hkval
      dsimp [b] at hkval
      calc
        k=2*(2*(2*q+1+2)) := hkval.symm
        _=8*(q+1)+4 := by ring
    · right; right
      have htime1 : 1≤time := by simpa only [zero_add] using lt_iff_succ_le.mp ht
      have htime1' : 1<time := lt_of_le_of_ne htime1 (Ne.symm h1)
      have htime2 : 2≤time := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp htime1'
      have htime2' : 2<time := lt_of_le_of_ne htime2 (Ne.symm h2)
      have htime3 : 3≤time := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp htime2'
      have hm := (y_strictMono b).monotone htime3
      rw [hy3] at hm
      have hm2 := add_le_add hm hm
      change (16*(q+1)*(q+1)+16*(q+1)+3)+(16*(q+1)*(q+1)+16*(q+1)+3) ≤
        ycoord time (2*q+1)+ycoord time (2*q+1) at hm2
      calc
        32*(q+1)*(q+1)+32*(q+1)+6 =
            (16*(q+1)*(q+1)+16*(q+1)+3)+(16*(q+1)*(q+1)+16*(q+1)+3) := by ring
        _ ≤ ycoord time (2*q+1)+ycoord time (2*q+1) := hm2
        _ = k := by rw [←hkval]; ring
theorem positive_parameter_trichotomy (Q x k : V) (hQ : 0<Q) (hk : 0<k)
    (hn : x*x=1+Q*(Q+1)*k*k) :
    k=2 ∨ k=8*Q+4 ∨ 32*Q*Q+32*Q+6 ≤ k := by
  have hQ1 : 1≤Q := by simpa using lt_iff_succ_le.mp hQ
  have he : Q-1+1=Q := tsub_add_cancel_of_le hQ1
  have hd : discriminant (Q-1)=Q*(Q+1) := by
    unfold discriminant
    rw [show Q-1+2=(Q-1+1)+1 by ring,he]
  have h := positive_norm_trichotomy (Q-1) x k hk (by rwa [hd])
  rw [he] at h
  exact h
end DiophantineConsistency.AdaptiveGap85PellTrichotomy
