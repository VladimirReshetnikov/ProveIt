import Trace74SeedOffsetJoin
import Trace74CRTNaturalTuple

/-! The CRT coordinate updates preserve the first-Pell seed inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CRTFirstPellJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74ChartAssembly
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Given the explicit CRT certificates and one first-Pell seed, the very
same CRT-updated natural tuple retains all strong-seed inputs. -/
theorem exists_first_pell_carrier (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (q0 h D c0 U W RJ k0 r bound : V)
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
    (hK : let p0 := fun i => (ι (p i:V) : DiffRing V);
      let v0 := fun i => (ι (v i) : DiffRing V);
      let Q := p0 0*v0 0+1; let X := v0 5*Q; let Y := (Q*Q*Q)*v0 6;
      let C := (v0 8+v0 9)*Y+v0 8; let H := 4*(X*Y+Y)-1;
      H ∣ X*(3*C-2*X)+2) :
    ∃ N : V, bound<N ∧
      let w := Function.update (Function.update v 1 1) 2 (q0*h+N)
      0<X p w ∧ 0<Y p w ∧ 0<c p w ∧
      2*ycoord n (2*(firstParam p w-1)+1)=k w ∧
      (chart (ports p) (fun i => ι (w i))).M ∣
        (chart (ports p) (fun i => ι (w i))).Z := by
  obtain ⟨N,hN,hdiv⟩ := Trace74CRTNaturalTuple.exists_updated_carrier
    (fun j => (p j:V)) v q0 h D c0 U W RJ k0 r bound
    hh hD hc0 hq hU hW hh0 hDshape hWshape hRJshape hkshape hUcast
    hDc hDh hch hUD hUc hWh hK
  let w := Function.update (Function.update v 1 1) 2 (q0*h+N)
  have hx : 0<X p w := by simpa [w,X,q,Trace75Factors.b,Function.update] using hX
  have hy : 0<Y p w := by simpa [w,Y,q,Trace75Factors.b,Function.update] using hY
  have hc' : 0<c p w := by simpa [w,c,k,Y,q,Trace75Factors.b,Function.update] using hc
  have hn' : 2*ycoord n (2*(firstParam p w-1)+1)=k w := by
    simpa [w,firstParam,X,Y,q,Trace75Factors.b,k,Function.update] using hn
  refine ⟨N,hN,hx,hy,hc',hn',?_⟩
  simpa only [ports,map_natCast] using hdiv

#print axioms Trace74CRTFirstPellJoin.exists_first_pell_carrier
end Trace74CRTFirstPellJoin
