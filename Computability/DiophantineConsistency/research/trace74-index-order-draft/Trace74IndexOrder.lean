import Trace74FirstIndexResidue
import Trace74Fold
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! UNCHECKED DRAFT. Guard-free ordering of actual 74 Pell indices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74IndexOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstIndex
open Trace75Factors Trace74Pell Trace74FirstIndexResidue Trace74Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_lt_odd (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1)) : n<r := by
  let P : V := firstParam p v
  let S : V := Y p v
  let A0 : V := A p v
  let B : V := 2*(P-1)+1
  change 2*ycoord n B=k v at hny
  change c p v=ycoord r (A0-1) at hc
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hS : 0<S := hY
  have hS1 : 1≤S := pos_iff_one_le.mp hS
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hP : 0<P := mul_pos hX (mul_pos hS hS)
  have hA : 0<A0 := add_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hXP : X p v+1≤2*X p v := by
    calc
      X p v+1≤X p v+X p v := by simpa only [add_comm] using _root_.add_le_add_left hX1 (X p v)
      _=2*X p v := by ring
  have hSsq : S≤S*S := le_mul_of_one_le_right (by simp) hS1
  have hA2P : A0≤2*P := calc
    A0=S*(X p v+1) := by dsimp [A0,A,S]; ring
    _≤S*(2*X p v) := mul_le_mul_of_nonneg_left hXP (by simp)
    _≤(S*S)*(2*X p v) := mul_le_mul_of_nonneg_right hSsq (by simp)
    _=2*P := by dsimp [P,firstParam,S]; ring
  have hbase : A0-1≤B := by
    apply (add_le_add_iff_right (2:V)).mp
    calc
      A0-1+2=A0+1 := by rw [show A0-1+2=(A0-1+1)+1 by ring,hA1]
      _≤2*P+1 := by simpa only [add_comm] using _root_.add_le_add_right hA2P (1:V)
      _=B+2 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hkC : k v<c p v := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
  have hnR : n<r := by
    by_contra hnR
    have hRn : r≤n := le_of_not_gt hnR
    have he : c p v≤k v := calc
      c p v=ycoord r (A0-1) := hc
      _≤ycoord n (A0-1) := (y_strictMono (A0-1)).monotone hRn
      _≤ycoord n B := (base_mono (A0-1) B hbase n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k v := hny
    exact (not_le_of_gt hkC) he
  exact hnR

theorem graph_ordered_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n r : V, 0<n ∧ 0<r ∧ r%2=1 ∧ n<r ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord r (A p v-1) ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  obtain ⟨n,hn,hny,hmod⟩ := graph_first_index_residue p v hb hv hz
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hx,hy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  exact ⟨n,r,hn,hr,hodd,graph_first_lt_odd p v n r hb hv hny hc,hny,hc,hmod⟩

#print axioms Trace74IndexOrder.graph_first_lt_odd
#print axioms Trace74IndexOrder.graph_ordered_indices
end Trace74IndexOrder
