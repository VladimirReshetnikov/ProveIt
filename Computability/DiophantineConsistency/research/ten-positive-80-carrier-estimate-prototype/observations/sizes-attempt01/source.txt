import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Elementary sufficient size bounds for the first carrier estimate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CarrierSizes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sufficient (D U tau f c : V)
    (hD : 16≤D) (hc : 1≤c) (hU : c≤U) (ht : 1≤tau)
    (hf : f*f=1+D*U*U*tau*tau) :
    let a := D*U*U*tau*tau
    let F := 1+2*a
    let Q := D*(4*a*(1+a))
    c<Q-1 ∧ 2*c<F ∧ 8*tau*f≤F := by
  let a : V := D*U*U*tau*tau
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  have hD1 : 1≤D := le_trans (by norm_num : (1:V)≤16) hD
  have hU1 : 1≤U := le_trans hc hU
  have ht2 : 1≤tau*tau := one_le_mul ht ht
  have hU2 : 1≤U*U := one_le_mul hU1 hU1
  have hca : c≤a := calc
    c≤U := hU
    _≤U*U := le_mul_of_one_le_right (by simp) hU1
    _≤D*(U*U) := le_mul_of_one_le_left (by simp) hD1
    _≤(D*(U*U))*(tau*tau) := le_mul_of_one_le_right (by simp) ht2
    _=a := by dsimp [a]; ring
  have hDUsq : 16≤D*(U*U) := le_trans hD (le_mul_of_one_le_right (by simp) hU2)
  have hsquare : (4*tau)*(4*tau)<f*f := calc
    (4*tau)*(4*tau)=16*(tau*tau) := by ring
    _≤(D*(U*U))*(tau*tau) := mul_le_mul_of_nonneg_right hDUsq (by simp)
    _=a := by dsimp [a]; ring
    _<1+a := by simp
    _=f*f := hf.symm
  have hfgap : 4*tau<f := lt_of_mul_self_lt_mul_self₀ (by simp) hsquare
  have hfpos : 0<f := lt_of_le_of_lt (by simp) hfgap
  have h8 : 8*tau*f<F+1 := calc
    8*tau*f=2*((4*tau)*f) := by ring
    _<2*(f*f) := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hfgap hfpos) (by norm_num)
    _=F+1 := by dsimp [F]; rw [hf]; dsimp [a]; ring
  have htfF : 8*tau*f≤F := by
    have h := lt_iff_succ_le.mp h8
    exact (add_le_add_iff_right (1:V)).mp h
  have hcF : 2*c<F := calc
    2*c≤2*a := mul_le_mul_of_nonneg_left hca (by simp)
    _<1+2*a := by simp
  have h4a : 4*a≤Q := calc
    4*a≤4*a*(1+a) := le_mul_of_one_le_right (by simp) (by simp)
    _≤D*(4*a*(1+a)) := le_mul_of_one_le_left (by simp) hD1
  have hc4 : c+1<4*c := by
    have hpos : 0<c := lt_of_lt_of_le (by simp) hc
    calc
      c+1≤c+c := by simpa only [add_comm] using add_le_add_left hc c
      _<c+c+(c+c) := lt_add_of_pos_right _ (add_pos hpos hpos)
      _=4*c := by ring
  have hcQ : c+1<Q := lt_of_lt_of_le hc4 (le_trans (mul_le_mul_of_nonneg_left hca (by simp)) h4a)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (le_trans (by simp : (1:V)≤c+1) (le_of_lt hcQ))
  have hcB : c<Q-1 := by
    apply (add_lt_add_iff_right (1:V)).mp
    rw [hQ1]
    exact hcQ
  exact ⟨hcB,hcF,htfF⟩

#print axioms CarrierSizes.sufficient
end CarrierSizes
