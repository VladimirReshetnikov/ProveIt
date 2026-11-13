import Trace74DynamicRegisters

/-! Derive both varying-register binding conditions from base components. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74DynamicBindings
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ModelDifferenceRing
open Trace74WitnessAssembly Trace74ChartAssembly Trace74DynamicRegisters
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem components_independent (p : Fin 4 → DiffRing V) (base : Fin 10 → V) (T n : V) :
    components p (fun l => ι (tuple base T n l))=components p (fun l => ι (base l)) := by
  rfl

theorem dynamic_forms_from_base
    (a t j I c N M C G P B : V) (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (hc : (components p (fun l => ι (base l))).c=ι c)
    (hr : (components p (fun l => ι (base l))).rank= -ι N)
    (hf : (components p (fun l => ι (base l))).f=ι (xcoord (2*t) a))
    (hb : (components p (fun l => ι (base l))).B=ι B)
    (ho : (components p (fun l => ι (base l))).offset=ι C-ι G)
    (hm : (chart p (fun l => ι (base l))).M=ι M) :
    (∀ T n : V, let v := tuple base T n
      (chart p (fun l => ι (v l))).V+ι c=ι (xcoord (2*t) a)*(ι c*ι T+ι N)) ∧
    (let f := xcoord (2*t) a
     let s := f*(N+c)+P+1
     let h := 2*(j+t*(2*s+1))
     let Q := oddQuotient h (I-2)
     ∀ T n : V, Q+c=f*(c*T+N) →
       let v := tuple base T n
       (chart p (fun l => ι (v l))).Z=ι M*(ι n-ι Q*ι Q*ι B)+(ι C-ι G)) := by
  have hV : ∀ T n : V, let v := tuple base T n
      (chart p (fun l => ι (v l))).V+ι c=ι (xcoord (2*t) a)*(ι c*ι T+ι N) := by
    intro T n
    have heq := V_formula p (fun l => ι (tuple base T n l))
    rw [components_independent p base T n, hc, hr, hf] at heq
    have ht : ι (tuple base T n 4)=ι T := by rfl
    rw [ht] at heq
    linear_combination heq
  refine ⟨hV, ?_⟩
  dsimp only
  intro T n heq
  have hcast := congrArg ι heq
  simp only [map_add,map_mul] at hcast
  have hv := hV T n
  have hveq : (chart p (fun l => ι (tuple base T n l))).V =
      ι (oddQuotient (2*(j+t*(2*(xcoord (2*t) a*(N+c)+P+1)+1))) (I-2)) := by
    linear_combination hv-hcast
  have hz := Z_formula p (fun l => ι (tuple base T n l))
  have h7 : ι (tuple base T n 7)=ι n := by rfl
  obtain ⟨_,_,_,hmi⟩ := Trace74StaticIndependence.static_independent p base T n
  rw [components_independent p base T n, hb, ho, hmi, hm, h7, hveq] at hz
  exact hz

#print axioms Trace74DynamicBindings.dynamic_forms_from_base
end Trace74DynamicBindings
