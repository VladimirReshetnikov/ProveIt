import Trace74StrongSeedChart
import Trace74PellGapBinding

/-! Actual first Pell square and chart values for one positive tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstSquareChart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The supplied first ordinate makes the actual first graph factor a
square. It is a same-tuple statement and assumes no graph zero. -/
theorem first_square (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hX : 0<X p v) (hY : 0<Y p v)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v) :
    let b := 2*(firstParam p v-1)+1
    0<xcoord n b ∧ E p v=xcoord n b*xcoord n b := by
  let P := firstParam p v
  let b := 2*(P-1)+1
  let y := ycoord n b
  let tau := xcoord n b
  have hp : 1≤P := by
    change 1≤X p v*(Y p v*Y p v)
    exact one_le_mul (pos_iff_one_le.mp hX)
      (one_le_mul (pos_iff_one_le.mp hY) (pos_iff_one_le.mp hY))
  have hP : P-1+1=P := tsub_add_cancel_of_le hp
  have hb1 : b+1=2*P := by
    dsimp [b]
    calc
      2*(P-1)+1+1=2*(P-1+1) := by ring
      _=2*P := by rw [hP]
  have hb3 : b+3=2*(P+1) := by
    calc
      b+3=(b+1)+2 := by ring
      _=2*P+2 := by rw [hb1]
      _=2*(P+1) := by ring
  have hd : ArithmeticPellRecurrence.delta b=4*P*(P+1) := by
    unfold ArithmeticPellRecurrence.delta
    rw [hb1,hb3]
    ring
  have hk : k v=2*y := hn.symm
  have hnorm : tau*tau=1+4*P*(P+1)*y*y := by
    dsimp [tau,y]
    simpa only [hd] using norm n b
  refine ⟨lt_of_lt_of_le (by norm_num) (one_le_x n b),?_⟩
  calc
    E p v=1+P*(P+1)*(k v)*(k v) := by dsimp [E,P,firstParam]; ring
    _=1+P*(P+1)*(2*y)*(2*y) := by rw [hk]
    _=1+4*P*(P+1)*y*y := by ring
    _=tau*tau := hnorm.symm

/-- For the actual chart tuple, the supplied first ordinate gives the base
square and the main discriminant identity used by the strong-seed client. -/
theorem base_chart_inputs (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hX : 0<X p v) (hY : 0<Y p v)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v) :
    ∃ tau : V, 0<tau ∧
      (components (ports p) (fun j => ι (v j))).c=ι (c p v) ∧
      (chart (ports p) (fun j => ι (v j))).E=ι tau*ι tau ∧
      (let w := fun j => ι (v j); let q0 := (ports p) 0*w 0+1;
        let Y0 := (q0*q0*q0)*w 6; let X0 := w 5*q0; let A0 := X0*Y0+Y0;
        A0*(A0+2)=ι (ArithmeticPellRecurrence.delta (A p v-1))) := by
  let b := 2*(firstParam p v-1)+1
  let tau := xcoord n b
  have hs := first_square p v n hX hY hn
  change 0<tau ∧ E p v=tau*tau at hs
  have hA : 1≤A p v := by
    have := add_pos (mul_pos hX hY) hY
    exact pos_iff_one_le.mp this
  have ha : A p v-1+1=A p v := tsub_add_cancel_of_le hA
  have hdelta : ArithmeticPellRecurrence.delta (A p v-1)=Trace75Factors.delta p v := by
    unfold ArithmeticPellRecurrence.delta Trace75Factors.delta
    have h3 : A p v-1+3=(A p v-1+1)+2 := by ring
    rw [h3,ha]
  refine ⟨tau,hs.1,?_,?_,?_⟩
  · simp only [components,ports,c,k,Y,q,Trace75Factors.b,map_mul,map_add,map_one,map_natCast]
  · change (regs (ports p) (fun j => ι (v j))).E=ι tau*ι tau
    rw [E_eval,hs.2,map_mul]
  · change (regs (ports p) (fun j => ι (v j))).Delta=ι (ArithmeticPellRecurrence.delta (A p v-1))
    rw [delta_eval,hdelta]

#print axioms Trace74FirstSquareChart.first_square
#print axioms Trace74FirstSquareChart.base_chart_inputs
end Trace74FirstSquareChart
