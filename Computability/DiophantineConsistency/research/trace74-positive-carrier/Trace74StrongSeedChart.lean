import Trace74StrongChartBinding
import Trace74CoupledPellStrongSeed

/-! Construct the strong seed and bind it to one updated 74-chart tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74StrongSeedChart
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellPeriodicity
open Trace74ChartAssembly Trace74DynamicRegisters Trace74StrongChartBinding
open Trace74CoupledPellStrongSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A divisible Pell seed binds the actual three strong chart fields after
updating coordinate 3. The base c, first square and main discriminant
identities remain explicit assumptions; no graph zero is asserted. -/
theorem exists_strong_chart (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (a c tau : V) (hc : 0<c) (htau : 0<tau)
    (hcbase : (components p (fun j => ι (base j))).c=ι c)
    (hebase : (chart p (fun j => ι (base j))).E=ι tau*ι tau)
    (hdelta : let v := fun j => ι (base j); let q := p 0*v 0+1;
      let Y := (q*q*q)*v 6; let X := v 5*q; let A := X*Y+Y;
      A*(A+2)=ι (delta a)) :
    ∃ t i : V, 0<t ∧ 0<i ∧ c∣t ∧ ycoord t a=(c*c*tau)*i ∧
      let f := xcoord (2*t) a
      let I := delta a*ycoord (2*t) a
      let phi := xcoord t a
      let v := Function.update base 3 i
      2≤I ∧ c∣I ∧ f%c=(1:V)%c ∧ I*I+delta a=delta a*f*f ∧
      (chart p (fun j => ι (v j))).F=ι phi*ι phi ∧
      (components p (fun j => ι (v j))).f=ι f ∧
      (chart p (fun j => ι (v j))).Q=ι I*ι I := by
  obtain ⟨t,i,ht,hi,hct,hiy,hI,hcI,hfmod,hnorm⟩ := exists_strong_seed a c tau hc htau
  let v := Function.update base 3 i
  let y := ycoord t a
  let phi := xcoord t a
  let f := xcoord (2*t) a
  let I := delta a*ycoord (2*t) a
  have hc' : (components p (fun j => ι (v j))).c=ι c := hcbase
  have he' : (chart p (fun j => ι (v j))).E=ι tau*ι tau := hebase
  have hd' : let w := fun j => ι (v j); let q := p 0*w 0+1;
      let Y := (q*q*q)*w 6; let X := w 5*q; let A := X*Y+Y;
      A*(A+2)=ι (delta a) := hdelta
  have hu : (ι (v 3)*(ι c*ι c))*ι tau=ι y := by
    have hi' : v 3=i := by simp [v]
    rw [hi']
    dsimp [y]
    rw [hiy]
    simp only [map_mul]
    ring
  have hphi : (ι phi:DiffRing V)*ι phi=1+ι (delta a)*ι y*ι y := by
    have hn := congrArg ι (norm t a)
    simpa only [phi,y,map_add,map_mul,map_one] using hn
  have hf : (ι f:DiffRing V)=2*ι phi*ι phi-1 := by
    have hd := congrArg ι (double_x t a)
    simp only [map_add,map_mul,map_one,map_ofNat] at hd
    dsimp [f,phi,y]
    dsimp [phi,y] at hphi
    linear_combination hd-2*hphi
  have hdouble : (ι I:DiffRing V)=2*ι (delta a)*ι phi*ι y := by
    dsimp [I,phi,y]
    rw [double_y]
    simp only [map_mul,map_ofNat]
    ring
  obtain ⟨hF,hf',hQ⟩ := graph_strong_outputs p (fun j => ι (v j))
    (ι (delta a)) (ι c) (ι tau) (ι y) (ι phi) (ι f) (ι I)
    hc' he' hd' hu hphi hf hdouble
  exact ⟨t,i,ht,hi,hct,hiy,hI,hcI,hfmod,hnorm,hF,hf',hQ⟩

#print axioms Trace74StrongSeedChart.exists_strong_chart
end Trace74StrongSeedChart
