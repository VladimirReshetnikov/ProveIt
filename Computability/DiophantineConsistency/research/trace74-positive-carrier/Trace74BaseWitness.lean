import Trace74DynamicBindings

/-! Positive trace74 witness from one base tuple and explicit component values. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74BaseWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ModelDifferenceRing
open Trace74WitnessAssembly Trace74ChartAssembly Trace74DynamicRegisters
open Trace74StaticBindings Trace74StaticIndependence Trace74DynamicBindings
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every displayed register assumption concerns the same fixed base tuple.
The theorem constructs the two dynamic coordinates and a positive zero. -/
theorem exists_positive_zero_from_base
    (a t j I c N M C G P S B tau phi : V)
    (p : Fin 4 → DiffRing V) (base : Fin 10 → V)
    (ht : 0<t) (hI : 2≤I) (hc : 0<c) (hB : 1≤B)
    (hnorm : I*I+delta a=delta a*(xcoord (2*t) a)*(xcoord (2*t) a))
    (hcI : c∣I) (hct : c∣t) (hcy : c=ycoord (4*j+1) a)
    (hN : N%c=(4*j+1)%c) (hfc : xcoord (2*t) a%c=(1:V)%c)
    (hdiv : ι C-ι G=ι M*(ι P-ι S))
    (hbase : ∀ l, l≠4 → l≠7 → 0<base l)
    (hQ : (chart p (fun l => ι (base l))).Q=ι I*ι I)
    (hE : (chart p (fun l => ι (base l))).E=ι tau*ι tau)
    (hF : (chart p (fun l => ι (base l))).F=ι phi*ι phi)
    (hM : (chart p (fun l => ι (base l))).M=ι M)
    (hcompc : (components p (fun l => ι (base l))).c=ι c)
    (hcompr : (components p (fun l => ι (base l))).rank= -ι N)
    (hcompf : (components p (fun l => ι (base l))).f=ι (xcoord (2*t) a))
    (hcompB : (components p (fun l => ι (base l))).B=ι B)
    (hcompo : (components p (fun l => ι (base l))).offset=ι C-ι G) :
    ∃ v : Fin 10 → V, (∀ l, 0<v l) ∧ Trace74Mask.value74 p (fun l => ι (v l))=0 := by
  have hstatic := static_from_base p base I tau phi M hQ hE hF hM
  obtain ⟨hV,hZ⟩ := dynamic_forms_from_base a t j I c N M C G P B p base
    hcompc hcompr hcompf hcompB hcompo hM
  have hbind := bindings_from_static a t j I c N M C G P B tau phi p base hbase hstatic hV hZ
  exact exists_positive_zero_of_bindings a t j I c N M C G P S B tau phi p base
    ht hI hc hB hnorm hcI hct hcy hN hfc hdiv hbind

#print axioms Trace74BaseWitness.exists_positive_zero_from_base
end Trace74BaseWitness
