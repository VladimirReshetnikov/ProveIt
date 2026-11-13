import Trace74FirstSquareStrongChart
import Trace74CarrierChartBinding

/-! Keep the carrier divisibilities on the same strong-seed tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74StrongCarrierChart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74ChartAssembly Trace74DynamicRegisters

def carrierInputs {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) : Prop :=
  (let B := (p 1+v 5)*v 2-v 1; p 0*v 0 ∣ B) ∧
  (let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
    let k := v 8+v 9; let G := q*(q-v 1)-v 2;
    let rank := G*(q*q-1)+(p 2+q*p 3)*v 0;
    X*Y ∣ k-rank-1) ∧
  (let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
    let c := (v 8+v 9)*Y+v 8; let H := 4*(X*Y+Y)-1;
    H ∣ X*(3*c-2*X)+2)

/-- The carrier inputs do not mention the coordinate chosen for the strong
Pell seed. -/
theorem carrierInputs_update_three {R : Type*} [CommRing R]
    (p : Fin 4 → R) (v : Fin 10 → R) (i : R) :
    carrierInputs p (Function.update v 3 i) ↔ carrierInputs p v := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- First-Pell and carrier inputs for a common tuple yield a strong seed and
carrier divisibility for the actual chart after the coordinate-3 update. -/
theorem exists_chart (p : Fin 4 → ℕ) (base : Fin 10 → V) (n : V)
    (hX : 0<X p base) (hY : 0<Y p base) (hc : 0<c p base)
    (hn : 2*ycoord n (2*(firstParam p base-1)+1)=k base)
    (hcarrier : carrierInputs (ports p) (fun j => ι (base j))) :
    ∃ tau t i : V, (0 < tau) ∧ (0 < t) ∧ (0 < i) ∧ (c p base ∣ t) ∧
      ycoord t (A p base-1)=(c p base*c p base*tau)*i ∧
      let f := xcoord (2*t) (A p base-1)
      let I := ArithmeticPellRecurrence.delta (A p base-1)*ycoord (2*t) (A p base-1)
      let phi := xcoord t (A p base-1)
      let v := Function.update base 3 i
      2≤I ∧ (c p base ∣ I) ∧ f%(c p base)=(1:V)%(c p base) ∧
      I*I+ArithmeticPellRecurrence.delta (A p base-1)=
        ArithmeticPellRecurrence.delta (A p base-1)*f*f ∧
      (chart (ports p) (fun j => ι (v j))).F=ι phi*ι phi ∧
      (components (ports p) (fun j => ι (v j))).f=ι f ∧
      (chart (ports p) (fun j => ι (v j))).Q=ι I*ι I ∧
      (chart (ports p) (fun j => ι (v j))).M ∣
        (chart (ports p) (fun j => ι (v j))).Z := by
  obtain ⟨tau,t,i,htau,ht,hi,hct,hy,hI,hcI,hf,hnorm,hF,hf',hQ⟩ :=
    Trace74FirstSquareStrongChart.exists_chart p base n hX hY hc hn
  have hcarrier' : carrierInputs (ports p) (fun j => ι ((Function.update base 3 i) j)) := by
    simpa [carrierInputs, Function.update] using hcarrier
  obtain ⟨hB,he,hK⟩ := hcarrier'
  have hd := Trace74CarrierChartBinding.actual_carrier_divisibility
    (ports p) (fun j => ι ((Function.update base 3 i) j)) hB he hK
  exact ⟨tau,t,i,htau,ht,hi,hct,hy,hI,hcI,hf,hnorm,hF,hf',hQ,hd⟩

#print axioms Trace74StrongCarrierChart.carrierInputs_update_three
#print axioms Trace74StrongCarrierChart.exists_chart
end Trace74StrongCarrierChart
