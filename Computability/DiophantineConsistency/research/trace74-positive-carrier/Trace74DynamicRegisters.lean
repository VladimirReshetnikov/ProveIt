import Trace74StaticIndependence

/-! Expose the actual trace74 V and Z register structure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74DynamicRegisters
open Trace74ChartAssembly

structure Components (R : Type*) where
  c : R
  rank : R
  f : R
  B : R
  offset : R

def components {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) : Components R :=
  let J := v 0
  let F := v 1
  let C := v 2
  let i := v 3
  let w := v 5
  let s := v 6
  let eta := v 8
  let zeta := v 9
  let bJ := p 0*J
  let q := bJ+1
  let q2 := q*q
  let Y := (q2*q)*s
  let X := w*q
  let k := eta+zeta
  let kY := k*Y
  let c := kY+eta
  let XY := X*Y
  let A := XY+Y
  let H := 4*A-1
  let E := (XY*kY)*(XY*kY+k)+1
  let rank := (q*(q-v 1)-C)*(q2-1)+(p 2+q*p 3)*J
  let B := (p 1+w)*C-F
  let U := i*(c*c)
  let d := A*(A+2)
  let f0 := (d*(U*E))*U
  let f := f0+(f0+1)
  let coeff := bJ*XY
  let K := X*(3*c-2*X)+2
  let offset := coeff*K-H*(XY*B+bJ*(k-rank-1))
  ⟨c,rank,f,B,offset⟩

theorem V_formula {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) :
    (chart p v).V+(components p v).c =
      (components p v).f*((components p v).c*v 4-(components p v).rank) := by
  simp only [chart,components,sub_add_cancel]

private theorem Z_identity {R : Type*} [CommRing R] (a H n V B K D h e : R) :
    a*(H*(n-V*V*B)+K)-H*(D*B+h*e) =
      (a*H)*(n-V*V*B)+(a*K-H*(D*B+h*e)) := by
  ring

theorem Z_formula {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) :
    (chart p v).Z = (chart p v).M*(v 7-(chart p v).V*(chart p v).V*(components p v).B)+
      (components p v).offset := by
  exact Z_identity _ _ _ _ _ _ _ _ _

#print axioms Trace74DynamicRegisters.V_formula
#print axioms Trace74DynamicRegisters.Z_formula
end Trace74DynamicRegisters
