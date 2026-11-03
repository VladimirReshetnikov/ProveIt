import Trace75ThreeBinding

/-! Explicit algebra remaining when the trace75 main index is three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75ThreeTwo
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace75Pell Trace75ThreeBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_three_two_algebra (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 3 (A p v-1)) :
    n=2 ∧ k v=8*X p v*(Y p v*Y p v)+4 ∧
    c p v+1=4*(A p v+1)*(A p v+1) ∧
    (ι (v 8):DiffRing V)+4*(ι (Y p v))^2 *
        ((ι (X p v))*(2*ι (Y p v)-ι (X p v)-2)-1) =
      4*ι (Y p v)*(2*ι (X p v)+1)+3 := by
  have hn := first_index_eq_two_of_main_three p v n hb hv hz hfirst hmain
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hp : 0<firstParam p v := mul_pos hx (mul_pos hy hy)
  have ha : 0<A p v := add_pos (mul_pos hx hy) hy
  have hp1 : firstParam p v-1+1=firstParam p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hp)
  have ha1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp ha)
  let B : V := 2*(firstParam p v-1)+1
  have hbase : B+2=2*firstParam p v+1 := by
    calc
      B+2=2*(firstParam p v-1+1)+1 := by dsimp [B]; ring
      _=2*firstParam p v+1 := by rw [hp1]
  have hbaseA : A p v-1+2=A p v+1 := by
    calc
      A p v-1+2=(A p v-1+1)+1 := by ring
      _=A p v+1 := by rw [ha1]
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy2 : ycoord 2 B=2*(B+2) := by
    calc
      ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
      _=2*(B+2) := by rw [hx1,hy1]; ring
  have hk : k v=8*X p v*(Y p v*Y p v)+4 := by
    change 2*ycoord n B=k v at hfirst
    rw [hn,hy2,hbase] at hfirst
    dsimp [firstParam] at hfirst
    calc
      k v=2*(2*(2*(X p v*(Y p v*Y p v))+1)) := hfirst.symm
      _=8*X p v*(Y p v*Y p v)+4 := by ring
  have hc : c p v+1=4*(A p v+1)*(A p v+1) := by
    rw [hmain]
    simpa only [hbaseA] using y_three (A p v-1)
  refine ⟨hn,hk,hc,?_⟩
  have hkcast := congrArg (fun z : V => (ι z : DiffRing V)) hk
  have hccast := congrArg (fun z : V => (ι z : DiffRing V)) hc
  simp only [c,k,A,map_add,map_mul,map_one,map_ofNat] at hkcast hccast
  linear_combination hccast - (ι (Y p v):DiffRing V)*hkcast

#print axioms Trace75ThreeTwo.graph_three_two_algebra
end Trace75ThreeTwo
