import Trace74WitnessAssembly

/-! Replace the full witness callback by static chart-register identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74StaticBindings
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ModelDifferenceRing
open Trace74WitnessAssembly Trace74ChartAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem tuple_positive (base : Fin 10 → V) (T n : V) (hT : 0<T) (hn : 0<n)
    (hbase : ∀ l, l≠4 → l≠7 → 0<base l) : ∀ l, 0<tuple base T n l := by
  intro l
  by_cases h4 : l=4
  · subst l; simpa [tuple] using hT
  by_cases h7 : l=7
  · subst l; simpa [tuple] using hn
  simpa [tuple,h4,h7] using hbase l h4 h7

/-- Static chart identities are all that remain to construct the binding
callback. The two varying registers are linear in T and the carrier. -/
theorem bindings_from_static
    (a t j I c N M C G P B tau phi : V)
    (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (hbase : ∀ l, l≠4 → l≠7 → 0<base l)
    (hstatic : ∀ T n : V,
      let v := tuple base T n
      (chart p (fun l => ι (v l))).Q=ι I*ι I ∧
      (chart p (fun l => ι (v l))).E=ι tau*ι tau ∧
      (chart p (fun l => ι (v l))).F=ι phi*ι phi ∧
      (chart p (fun l => ι (v l))).M=ι M)
    (hVform : ∀ T n : V,
      let v := tuple base T n
      (chart p (fun l => ι (v l))).V+ι c=
        ι (xcoord (2*t) a)*(ι c*ι T+ι N))
    (hZform :
      let f := xcoord (2*t) a
      let s := f*(N+c)+P+1
      let h := 2*(j+t*(2*s+1))
      let Q := oddQuotient h (I-2)
      ∀ T n : V, Q+c=f*(c*T+N) →
        let v := tuple base T n
        (chart p (fun l => ι (v l))).Z=
          ι M*(ι n-ι Q*ι Q*ι B)+(ι C-ι G)) :
    let f := xcoord (2*t) a
    let s := f*(N+c)+P+1
    let h := 2*(j+t*(2*s+1))
    let Q := oddQuotient h (I-2)
    let y := ycoord (2*h+1) (I-2)
    ∀ T n : V, 0<T → 0<n → Q+c=f*(c*T+N) →
      ι M*(ι n-ι Q*ι Q*ι B)+(ι C-ι G)=ι M*(ι tau*ι phi*ι y) →
      let v := tuple base T n
      (∀ l, 0<v l) ∧
      (chart p (fun l => ι (v l))).Q=ι I*ι I ∧
      (chart p (fun l => ι (v l))).E=ι tau*ι tau ∧
      (chart p (fun l => ι (v l))).F=ι phi*ι phi ∧
      (chart p (fun l => ι (v l))).V=ι Q ∧
      (chart p (fun l => ι (v l))).Z=(chart p (fun l => ι (v l))).M*ι tau*ι phi*ι y := by
  dsimp only
  intro T n hT hn hTeq hneq
  obtain ⟨hQ,hE,hF,hM⟩ := hstatic T n
  have htcast := congrArg ι hTeq
  simp only [map_add,map_mul] at htcast
  have hV := hVform T n
  have hVeq : (chart p (fun l => ι (tuple base T n l))).V =
      ι (oddQuotient (2*(j+t*(2*(xcoord (2*t) a*(N+c)+P+1)+1))) (I-2)) := by
    linear_combination hV-htcast
  have hZ := hZform T n hTeq
  rw [hneq, ← hM] at hZ
  refine ⟨tuple_positive base T n hT hn hbase,hQ,hE,hF,hVeq,?_⟩
  linear_combination hZ

#print axioms Trace74StaticBindings.bindings_from_static
end Trace74StaticBindings
