import Trace74ChartAssembly

/-! Conditional same-tuple witness assembly from explicit register bindings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74WitnessAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ModelDifferenceRing
open Trace74CoupledCarrierShift Trace74ChartAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tuple (base : Fin 10 → V) (T n : V) : Fin 10 → V :=
  Function.update (Function.update base 4 T) 7 n

/-- The hypotheses explicitly bind all five required chart fields to the
constructed coordinates, for the same actual tuple. They do not assume a graph
zero. Discharging them for the fixed ports is a separate obligation. -/
theorem exists_positive_zero_of_bindings
    (a t j I c N M C G P S B tau phi : V)
    (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (ht : 0<t) (hI : 2≤I) (hc : 0<c) (hB : 1≤B)
    (hnorm : I*I+delta a=delta a*(xcoord (2*t) a)*(xcoord (2*t) a))
    (hcI : c∣I) (hct : c∣t) (hcy : c=ycoord (4*j+1) a)
    (hN : N%c=(4*j+1)%c) (hfc : xcoord (2*t) a%c=(1:V)%c)
    (hdiv : ι C-ι G=ι M*(ι P-ι S))
    (hbind :
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
        (chart p (fun l => ι (v l))).Z=(chart p (fun l => ι (v l))).M*ι tau*ι phi*ι y) :
    ∃ v : Fin 10 → V, (∀ l, 0<v l) ∧ Trace74Mask.value74 p (fun l => ι (v l))=0 := by
  let f := xcoord (2*t) a
  let s := f*(N+c)+P+1
  let h := 2*(j+t*(2*s+1))
  let Q := oddQuotient h (I-2)
  let y := ycoord (2*h+1) (I-2)
  obtain ⟨T,n,hT,hn,hTeq,hneq⟩ :=
    positive_T_and_carrier a t j I c N M C G P S B tau phi y
      ht hI hc hB hnorm hcI hct hcy hN hfc hdiv
  obtain ⟨hv,hQ,hE,hF,hV,hZ⟩ := hbind T n hT hn hTeq hneq
  exact ⟨tuple base T n,hv,zero_of_same_orbit p (tuple base T n) I h tau phi hI hQ hE hF hV hZ⟩

#print axioms Trace74WitnessAssembly.exists_positive_zero_of_bindings
end Trace74WitnessAssembly
