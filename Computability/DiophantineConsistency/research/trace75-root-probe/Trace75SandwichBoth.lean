import Trace75SandwichLower
import PellScaledUpper
import Trace75GraphPower
import DiophantineConsistency.ArithmeticHalfBinomial

/-! Both scaled Pell sandwiches at the same actual graph rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75SandwichBoth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomial
open Trace75Factors Trace75Rank Trace75RankExact Trace75Pell
open Trace75IndexAlignment Trace75SandwichLower TenPositivePellScaledUpper
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_sandwich_both (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (h31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r : V, 0<r ∧ rankNat p v=2*r+1 ∧ X p v=Exp.exp (2*r+1) ∧
      k v*power (X p v+1) (2*r)<2*c p v*power (X p v) r ∧
      2*c p v*power (X p v) r<k v*(power (X p v+1) (2*r)+power (X p v) r) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) h31
  obtain ⟨r,hr,hR,hlow⟩ := graph_sandwich_lower p v h31 hl hh hv hz
  obtain ⟨n,_hn,_hnR,heq,hny,hc⟩ := graph_first_main_alignment p v h31 hl hh hv hz
  have hne : 2*n=2*(r+1) := by rw [heq,hR]; ring
  have hnr : n=r+1 := mul_left_cancel₀ (by norm_num : (2:V)≠0) hne
  have hp := Trace75GraphPower.graph_power p v h31 hl hh hv hz
  have hXeq : X p v=Exp.exp (2*r+1) := by rwa [hR] at hp
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq32 : (32:V)≤q p v := by
    unfold q b
    calc
      (32:V)=31*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul h31 hj (by simp) (by simp)) 1
  have h41 : (41:V)≤rankNat p v := le_trans (by norm_num : (41:V)≤3*32)
    (le_trans (mul_le_mul_of_nonneg_left hq32 (by simp)) (le_of_lt (graph_rank_exact p v h31 hl hh hv hz).2.1))
  have hr20 : (20:V)≤r := by
    have h2 : (2:V)*20≤2*r := (add_le_add_iff_right (1:V)).mp (by
      simpa only [show (2:V)*20+1=41 by ring,←hR] using h41)
    exact le_of_mul_le_mul_left h2 (by norm_num : (0:V)<2)
  have hr4 : 4≤r := le_trans (by norm_num) hr20
  have h24 : 24*r<X p v+1 := by
    have h72 := seventy_two_lt_exp r hr4
    rw [←hXeq] at h72
    have hle : 24*r≤72*r := mul_le_mul_of_nonneg_right (by norm_num : (24:V)≤72) (by simp)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le h72 (by simp))
  let S : V := Y p v
  let P : V := firstParam p v
  let A0 : V := S*(X p v+1)
  let a : V := A p v-1
  let B : V := 2*(P-1)+1
  let N : V := power (X p v+1) (2*r)
  let D : V := power (X p v) r
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hS : 1≤S := pos_iff_one_le.mp hY
  have hSY : Y p v≤S := le_refl _
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hAeq : A p v=A0 := by dsimp [A,A0,S]; ring
  have hA0 : 0<A0 := by rw [←hAeq]; exact hA
  have hA1 : a+1=A0 := by rw [←hAeq]; exact tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have ha : a+2=A0+1 := by rw [show a+2=(a+1)+1 by ring,hA1]
  have hB : 2*B+3=4*X p v*S*S+1 := calc
    2*B+3=4*(P-1+1)+1 := by dsimp [B]; ring
    _=4*P+1 := by rw [hP1]
    _=4*X p v*S*S+1 := by dsimp [P,firstParam,S]; ring
  have hcoeff : (2*(a+2))*(2*(a+2))*X p v*A0≤
      (2*B+3)*((X p v+1)*(X p v+1))*(A0+3) := by
    rw [ha,hB]
    exact shifted_upper_coefficient (X p v) S hX1 hS
  have hpert : 2*r*3≤A0 := by
    have h6 : 2*r*3≤24*r := by
      have hh6 : (6:V)≤24 := by norm_num
      simpa only [show 2*r*3=6*r by ring] using mul_le_mul_of_nonneg_right hh6 (by simp)
    have hXA : X p v+1≤A0 := le_mul_of_one_le_left (by simp) hS
    exact le_trans h6 (le_trans (le_of_lt h24) hXA)
  have hkpos : 0<k v := add_pos (hv 8) (hv 9)
  have hDpos : 0<D := power_pos (X p v) r hX
  have hint : c p v<k v*(Y p v+1) := by
    change k v*Y p v+v 8<k v*(Y p v+1)
    have he : v 8<k v := lt_add_of_pos_right _ (hv 9)
    have hs := add_lt_add_of_le_of_lt (le_refl (k v*Y p v)) he
    simpa only [mul_add,mul_one] using hs
  have hN : N<2*(Y p v+1)*D := by
    apply (mul_lt_mul_iff_of_pos_left hkpos).mp
    calc
      k v*N<2*c p v*D := hlow
      _<2*(k v*(Y p v+1))*D := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hint (by simp)) hDpos
      _=k v*(2*(Y p v+1)*D) := by ring
  have hcrude : 2*r*3*N<A0*D := by
    have hYY : Y p v+1≤2*Y p v := by
      calc
        Y p v+1≤Y p v+Y p v := by simpa only [add_comm] using _root_.add_le_add_left hY1 (Y p v)
        _=2*Y p v := by ring
    have hra : 24*r*Y p v<A0 := calc
      24*r*Y p v<(X p v+1)*Y p v := mul_lt_mul_of_pos_right h24 hY
      _≤(X p v+1)*S := mul_le_mul_of_nonneg_left hSY (by simp)
      _=A0 := by dsimp [A0]; ring
    calc
      2*r*3*N<2*r*3*(2*(Y p v+1)*D) := mul_lt_mul_of_pos_left hN (mul_pos (mul_pos (by simp) hr) (by simp))
      _=12*r*((Y p v+1)*D) := by ring
      _≤12*r*((2*Y p v)*D) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hYY (by simp)) (by simp)
      _=(24*r*Y p v)*D := by ring
      _<A0*D := mul_lt_mul_of_pos_right hra hDpos
  have hupper := upper_of_bounds (X p v) r a B A0 hA0 hcoeff hpert hcrude
  change 2*ycoord n B=k v at hny
  rw [hnr] at hny
  change c p v=ycoord (rankNat p v) a at hc
  rw [hR] at hc
  rw [hny,←hc] at hupper
  exact ⟨r,hr,hR,hXeq,hlow,hupper⟩

#print axioms Trace75SandwichBoth.graph_sandwich_both
end Trace75SandwichBoth
