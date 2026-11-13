import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011

/-! Unchecked draft: first index < main index without the early carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFirstIndexComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
open ArithmeticAdaptiveIndexComparison2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_lt_main (X Y k eta n m : V)
    (hX : 0<X) (hY : 2≤Y) (heta : 0<eta)
    (hfirst : 2*ycoord n (2*((X*Y)*Y-1)+1)=k)
    (hmain : ycoord m (X*Y+Y)=k*Y+eta) : n<m := by
  let E : V := X*Y
  let Q : V := E*Y
  let B : V := 2*(Q-1)+1
  let a : V := E+Y
  have hY0 : 0<Y := lt_of_lt_of_le (by norm_num) hY
  have hE : 0<E := mul_pos hX hY0
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE hY0))
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc 2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have heq : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by
            dsimp [a]; rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have heq' : a+2≤B+2 := by rw [←heq]; simp [add_assoc]
    exact (add_le_add_iff_right (2:V)).mp heq'
  have hkc : k<k*Y+eta := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+eta := lt_add_of_pos_right _ heta
  change 2*ycoord n B=k at hfirst
  change ycoord m a=k*Y+eta at hmain
  by_contra hn
  have hm : m≤n := le_of_not_gt hn
  have hcle : k*Y+eta≤k := calc
    k*Y+eta=ycoord m a := hmain.symm
    _≤ycoord n a := (y_strictMono a).monotone hm
    _≤ycoord n B := (base_mono a B hab n).2
    _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
    _=k := hfirst
  exact (not_le_of_gt hkc) hcle

#print axioms first_lt_main
end FreeMainFirstIndexComparison
