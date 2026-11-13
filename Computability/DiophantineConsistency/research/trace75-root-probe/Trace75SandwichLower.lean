import PellScaledSandwich
import Trace75VariableHeight

/-! Lower half-binomial sandwich at the actual 80 graph's scaled bases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75SandwichLower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace75Rank Trace75Pell Trace75IndexAlignment Trace75VariableHeight TenPositivePellScaledSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_sandwich_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r : V, 0<r ∧ rankNat p v=2*r+1 ∧
      k v*power (X p v+1) (2*r)<2*c p v*power (X p v) r := by
  obtain ⟨r,hr,hR,_hpow,_hheight⟩ := graph_variable_height p v hb31 hl hh hv hz
  obtain ⟨n,_hn,_hnR,heq,hny,hc⟩ := graph_first_main_alignment p v hb31 hl hh hv hz
  have hne : 2*n=2*(r+1) := by rw [heq,hR]; ring
  have hnr : n=r+1 := mul_left_cancel₀ (by norm_num : (2:V)≠0) hne
  let S : V := Y p v
  let P : V := firstParam p v
  let a : V := A p v-1
  let B : V := 2*(P-1)+1
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hS : 1≤S := pos_iff_one_le.mp hY
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hA1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hB : B+2=2*X p v*S*S+1 := calc
    B+2=2*(P-1+1)+1 := by dsimp [B]; ring
    _=2*P+1 := by rw [hP1]
    _=2*X p v*S*S+1 := by dsimp [P,firstParam,S]; ring
  have ha : 2*a+3=2*(S*(X p v+1))+1 := calc
    2*a+3=2*(a+1)+1 := by ring
    _=2*A p v+1 := by rw [hA1]
    _=2*(S*(X p v+1))+1 := by dsimp [A,S]; ring
  have hgap : 2*(B+2)*((X p v+1)*(X p v+1))<
      (2*a+3)*(2*a+3)*(X p v) := by
    rw [hB,ha]
    exact shifted_coefficient (X p v) S hX1 hS
  have hlow := lower_of_gap (X p v) r a B (pos_iff_one_le.mp hr) hgap
  change 2*ycoord n B=k v at hny
  rw [hnr] at hny
  change c p v=ycoord (rankNat p v) a at hc
  rw [hR] at hc
  rw [hny,←hc] at hlow
  exact ⟨r,hr,hR,hlow⟩

#print axioms Trace75SandwichLower.graph_sandwich_lower
end Trace75SandwichLower
