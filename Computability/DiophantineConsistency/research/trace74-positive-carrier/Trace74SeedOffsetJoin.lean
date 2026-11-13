import Trace74CarrierUpdate

/-! Carry an existing chart divisibility through the strong-seed update. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74SeedOffsetJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One base tuple satisfying the first-Pell and carrier conditions produces
a strong-seed tuple with the signed offset quotient used by the witness. -/
theorem exists_seed_offset (p : Fin 4 → ℕ) (base : Fin 10 → V) (n : V)
    (hX : 0<X p base) (hY : 0<Y p base) (hc : 0<c p base)
    (hn : 2*ycoord n (2*(firstParam p base-1)+1)=k base)
    (hdiv : (chart (ports p) (fun j => ι (base j))).M ∣
      (chart (ports p) (fun j => ι (base j))).Z) :
    ∃ tau t i C G P S : V, (0 < tau) ∧ (0 < t) ∧ (0 < i) ∧ (c p base ∣ t) ∧
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
      (chart (ports p) (fun j => ι (v j))).E=ι tau*ι tau ∧
      (components (ports p) (fun j => ι (v j))).c=ι (c p base) ∧
      (components (ports p) (fun j => ι (v j))).offset=ι C-ι G ∧
      ι C-ι G=ι (M p v)*(ι P-ι S) := by
  obtain ⟨tau,htau,hcbase,hebase,hdelta⟩ :=
    Trace74FirstSquareChart.base_chart_inputs p base n hX hY hn
  obtain ⟨t,i,ht,hi,hct,hy,hI,hcI,hf,hnorm,hF,hf',hQ⟩ :=
    Trace74StrongSeedChart.exists_strong_chart (ports p) base
      (A p base-1) (c p base) tau hc htau hcbase hebase hdelta
  let v := Function.update base 3 i
  have hE : (chart (ports p) (fun j => ι (v j))).E=ι tau*ι tau := by
    simpa [v,chart,Function.update] using hebase
  have hC : (components (ports p) (fun j => ι (v j))).c=ι (c p base) := by
    simpa [v,components,Function.update] using hcbase
  have hcast : (fun j => (ι (v j) : DiffRing V)) =
      Function.update (fun j => ι (base j)) 3 (ι i) := by
    funext j
    by_cases hj : j=3 <;> simp [v,hj]
  have hvdiv : (chart (ports p) (fun j => ι (v j))).M ∣
      (chart (ports p) (fun j => ι (v j))).Z := by
    rw [hcast]
    exact Trace74CarrierUpdate.update_three (ports p) (fun j => ι (base j)) (ι i) hdiv
  have hx : 0<X p v := by simpa [v,X,q,Trace75Factors.b,Function.update] using hX
  have hy' : 0<Y p v := by simpa [v,Y,q,Trace75Factors.b,Function.update] using hY
  obtain ⟨C,G,P,S,hoff,hquot⟩ := Trace74OffsetNatural.signed_offset p v hx hy' hvdiv
  exact ⟨tau,t,i,C,G,P,S,htau,ht,hi,hct,hy,hI,hcI,hf,hnorm,hF,hf',hQ,hE,hC,hoff,hquot⟩

#print axioms Trace74SeedOffsetJoin.exists_seed_offset
end Trace74SeedOffsetJoin
