import Trace74FirstSquareChart

/-! Assemble the first-Pell square and the strong chart for one tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FirstSquareStrongChart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A supplied first Pell ordinate gives a strong seed and binds its three
outputs to the actual chart after updating coordinate 3. -/
theorem exists_chart (p : Fin 4 → ℕ) (base : Fin 10 → V) (n : V)
    (hX : 0<X p base) (hY : 0<Y p base) (hc : 0<c p base)
    (hn : 2*ycoord n (2*(firstParam p base-1)+1)=k base) :
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
      (chart (ports p) (fun j => ι (v j))).Q=ι I*ι I := by
  obtain ⟨tau,htau,hcbase,hebase,hdelta⟩ :=
    Trace74FirstSquareChart.base_chart_inputs p base n hX hY hn
  obtain ⟨t,i,ht,hi,hct,hy,hrest⟩ :=
    Trace74StrongSeedChart.exists_strong_chart (ports p) base
      (A p base-1) (c p base) tau hc htau hcbase hebase hdelta
  exact ⟨tau,t,i,htau,ht,hi,hct,hy,hrest⟩

#print axioms Trace74FirstSquareStrongChart.exists_chart
end Trace74FirstSquareStrongChart
