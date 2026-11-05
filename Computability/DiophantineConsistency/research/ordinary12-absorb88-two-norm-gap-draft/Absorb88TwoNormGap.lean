import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Draft: a first/main Pell gap with no transport hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88TwoNormGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellClassification
open ArithmeticPellCongruences ArithmeticPellHalfIndex ArithmeticPellFirstNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gap (X Y k eta zeta tau g : V)
    (hX : 0 < X) (hY : 0 < Y) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hk : k = eta+zeta)
    (hfirst : tau*tau = 1+((X*Y)*Y)*(((X*Y)*Y)+1)*k*k)
    (hmain : g*g = 1+delta (X*Y+Y)*(eta+Y*k)*(eta+Y*k)) :
    8*((X*Y)*Y)+4 ≤ k := by
  let P : V := (X*Y)*Y
  let B : V := 2*(P-1)+1
  let a : V := X*Y+Y
  let c : V := eta+Y*k
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hD : discriminant (P-1)=P*(P+1) := by
    unfold discriminant
    rw [show P-1+2=(P-1+1)+1 by ring,hP1]
  have hf : tau*tau=1+discriminant (P-1)*k*k := by
    rw [hD]
    exact hfirst
  obtain ⟨n,_,_,_,_,hnk,_,_⟩ := solution_residues (P-1) tau k hf
  change 2*ycoord n B=k at hnk
  have hk0 : 0<k := by rw [hk]; exact add_pos heta hzeta
  have hn0 : 0<n := by
    by_contra hn
    have : n=0 := le_antisymm (le_of_not_gt hn) (by simp)
    subst n
    simp at hnk
    rw [← hnk] at hk0
    exact (not_lt_of_ge (le_refl (0:V))) hk0
  have hn1 : 1≤n := pos_iff_one_le.mp hn0
  have hn2 : 2≤n := by
    by_contra hn
    have hnle : n≤1 := lt_two_iff_le_one.mp (lt_of_not_ge hn)
    have hne : n=1 := le_antisymm hnle hn1
    have hyone : ycoord (1:V) B=1 := by
      simpa using (y_succ (0:V) B)
    have hk2 : k=2 := by rw [hne,hyone] at hnk; simpa using hnk.symm
    have he1 : 1≤eta := pos_iff_one_le.mp heta
    have hz1 : 1≤zeta := pos_iff_one_le.mp hzeta
    have heq : eta+zeta=2 := hk.symm.trans hk2
    have hetale : eta≤1 := by
      apply (add_le_add_iff_right (1:V)).mp
      calc
        eta+1≤eta+zeta := by simpa [add_comm] using (add_le_add_left hz1 eta)
        _=1+1 := by rw [heq]; norm_num
    have hetaone : eta=1 := le_antisymm hetale he1
    have hc : c=1+Y*2 := by dsimp [c]; rw [hetaone,hk2]
    have hm : g*g=1+delta a*c*c := hmain
    obtain ⟨m,_,_,hmc⟩ := ArithmeticPellClassification.solution_index a g c hm
    have hcone : 1<c := by rw [hc]; exact lt_add_of_pos_right 1 (mul_pos hY (by simp))
    have hm2 : 2≤m := by
      by_contra hm2
      have hmle : m≤1 := lt_two_iff_le_one.mp (lt_of_not_ge hm2)
      have hmy := (y_strictMono a).monotone hmle
      have haone : ycoord (1:V) a=1 := by simpa using (y_succ (0:V) a)
      rw [hmc,haone] at hmy
      exact (not_lt_of_ge hmy) hcone
    have hmy := (y_strictMono a).monotone hm2
    rw [y_two,hmc] at hmy
    have hclt : c < 2*(a+2) := by
      have haY : Y≤a := by dsimp [a]; exact le_add_self
      calc
        c=2*Y+1 := by rw [hc]; ring
        _<2*Y+4 := by simpa [add_comm] using (add_lt_add_left (by norm_num : (1:V)<4) (2*Y))
        _=2*(Y+2) := by ring
        _≤2*(a+2) := mul_le_mul_of_nonneg_left (by simpa [add_comm] using (add_le_add_right haY 2)) (by simp)
    exact (not_lt_of_ge hmy) hclt
  have hy := (y_strictMono B).monotone hn2
  rw [y_two] at hy
  have hle := mul_le_mul_of_nonneg_left hy (show (0:V)≤2 by simp)
  rw [hnk] at hle
  have hB : B+2=2*P+1 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
  rw [hB] at hle
  have heq : 2*(2*(2*P+1))=8*P+4 := by ring
  rw [heq] at hle
  exact hle

#print axioms Absorb88TwoNormGap.gap
end Absorb88TwoNormGap
