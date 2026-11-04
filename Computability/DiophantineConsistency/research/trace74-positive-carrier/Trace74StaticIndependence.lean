import Trace74StaticBindings

/-! The four static registers ignore both updated coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74StaticIndependence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace74WitnessAssembly Trace74ChartAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem static_independent (p : Fin 4 → DiffRing V) (base : Fin 10 → V) (T n : V) :
    let v := tuple base T n
    (chart p (fun l => ι (v l))).Q=(chart p (fun l => ι (base l))).Q ∧
    (chart p (fun l => ι (v l))).E=(chart p (fun l => ι (base l))).E ∧
    (chart p (fun l => ι (v l))).F=(chart p (fun l => ι (base l))).F ∧
    (chart p (fun l => ι (v l))).M=(chart p (fun l => ι (base l))).M := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem static_from_base (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (I tau phi M : V)
    (hQ : (chart p (fun l => ι (base l))).Q=ι I*ι I)
    (hE : (chart p (fun l => ι (base l))).E=ι tau*ι tau)
    (hF : (chart p (fun l => ι (base l))).F=ι phi*ι phi)
    (hM : (chart p (fun l => ι (base l))).M=ι M) :
    ∀ T n : V, let v := tuple base T n
      (chart p (fun l => ι (v l))).Q=ι I*ι I ∧
      (chart p (fun l => ι (v l))).E=ι tau*ι tau ∧
      (chart p (fun l => ι (v l))).F=ι phi*ι phi ∧
      (chart p (fun l => ι (v l))).M=ι M := by
  intro T n
  obtain ⟨q,e,f,m⟩ := static_independent p base T n
  exact ⟨q.trans hQ,e.trans hE,f.trans hF,m.trans hM⟩

#print axioms Trace74StaticIndependence.static_from_base
end Trace74StaticIndependence
