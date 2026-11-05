import Trace74CRTFirstPellJoin
import Trace74PellCarrierGraph

/-! Replace the CRT carrier factor by actual internal Pell bindings. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CRTPellFactorJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74ChartAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact graph carrier factor follows from three explicit same-tuple
Pell bindings; all CRT certificates and first-Pell inputs remain explicit. -/
theorem exists_first_pell_carrier (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (q0 h D c0 U W RJ k0 r bound bP nP : V)
    (hX : 0<X p v) (hY : 0<Y p v) (hc : 0<c p v)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hh : 0<h) (hD : 0<D) (hc0 : 0<c0)
    (hq : h+1=q0) (hU : 1≤U) (hW : 1≤W)
    (hh0 : h=(p 0:V)*v 0)
    (hDshape : D=(v 5*q0)*((q0*q0*q0)*v 6))
    (hWshape : W=(p 1:V)+v 5)
    (hRJshape : RJ=((p 2:V)+q0*(p 3:V))*v 0)
    (hkshape : k0=v 8+v 9)
    (hUcast : (ι U : DiffRing V)=ι q0*ι q0-1)
    (hDc : IsCoprime (ι D : DiffRing V) (ι c0))
    (hDh : IsCoprime (ι D : DiffRing V) (ι h))
    (hch : IsCoprime (ι c0 : DiffRing V) (ι h))
    (hUD : IsCoprime (ι U : DiffRing V) (ι D))
    (hUc : IsCoprime (ι U : DiffRing V) (ι c0))
    (hWh : IsCoprime (ι W : DiffRing V) (ι h))
    (hXP : X p v=power 2 nP)
    (hCP : c p v=ycoord nP bP)
    (hAP : A p v=bP+1) :
    ∃ N : V, bound<N ∧
      let w := Function.update (Function.update v 1 1) 2 (q0*h+N)
      0<X p w ∧ 0<Y p w ∧ 0<c p w ∧
      2*ycoord n (2*(firstParam p w-1)+1)=k w ∧
      (chart (ports p) (fun i => ι (w i))).M ∣
        (chart (ports p) (fun i => ι (w i))).Z := by
  have hK := Trace74PellCarrierGraph.graph_carrier_factor
    (fun j => (p j:V)) v bP nP hXP hCP hAP
  exact Trace74CRTFirstPellJoin.exists_first_pell_carrier p v n q0 h D c0 U W RJ k0 r bound
    hX hY hc hn hh hD hc0 hq hU hW hh0 hDshape hWshape hRJshape hkshape hUcast
    hDc hDh hch hUD hUc hWh hK

#print axioms Trace74CRTPellFactorJoin.exists_first_pell_carrier
end Trace74CRTPellFactorJoin
