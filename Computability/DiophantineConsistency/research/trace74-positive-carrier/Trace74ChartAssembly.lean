import Trace74AuxiliarySameOrbit
import Trace74Mask

/-! Same-tuple zero assembly under explicit chart-register bindings. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74ChartAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex ModelDifferenceRing
open Trace74AuxiliarySameOrbit

structure Chart (R : Type*) where
  Q : R
  Z : R
  M : R
  E : R
  F : R
  V : R

def chart {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) : Chart R :=
  let J := v 0
  let F := v 1
  let C := v 2
  let i := v 3
  let T := v 4
  let w := v 5
  let s := v 6
  let n := v 7
  let eta := v 8
  let zeta := v 9
  let bJ := p 0 * J
  let q := bJ + 1
  let q2 := q*q
  let q3 := q2*q
  let Y := q3*s
  let qmF := q-F
  let X := w*q
  let k := eta+zeta
  let kY := k*Y
  let c := kY+eta
  let XY := X*Y
  let Am1 := XY+Y
  let Hp := 4*Am1-1
  let Ap1 := Am1+2
  let V0k := XY*kY
  let V0kk := V0k+k
  let Dtau := V0k*V0kk+1
  let G := q*qmF-C
  let R := G*(q2-1)+(p 2+q*p 3)*J
  let e := k-R-1
  let Bt := (p 1+w)*C-F
  let U := i*(c*c)
  let Delta := Am1*Ap1
  let DpI2 := (Delta*(U*Dtau))*U
  let Df := DpI2+1
  let trace_f := DpI2+Df
  let Q := Delta*(4*(DpI2*Df))
  let V := trace_f*(c*T-R)-c
  let P1mu2 := bJ*XY
  let Kpos := X*(3*c-2*X)+2
  let Z := P1mu2*(Hp*(n-(V*V)*Bt)+Kpos)-Hp*(XY*Bt+bJ*e)
  let M := P1mu2*Hp
  ⟨Q,Z,M,Dtau,Df,V⟩

theorem output_chart {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 10 → R) :
    Trace74Mask.value74 p v =
      (chart p v).Q*((chart p v).Z*(chart p v).Z-
        (chart p v).M*(chart p v).M*((chart p v).E*(chart p v).F)*
          ((chart p v).V*(chart p v).V)) +
      ((chart p v).M*(chart p v).M*((chart p v).E*(chart p v).F)-
        (chart p v).Z*(chart p v).Z) := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For a single tuple, the exact chart bindings and the same-orbit Pell
identity imply output zero. Positivity and all bindings remain hypotheses. -/
theorem zero_of_same_orbit (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (I h tau phi : V) (hI : 2≤I)
    (hQ : (chart p (fun j => ι (v j))).Q=ι I*ι I)
    (hE : (chart p (fun j => ι (v j))).E=ι tau*ι tau)
    (hF : (chart p (fun j => ι (v j))).F=ι phi*ι phi)
    (hV : (chart p (fun j => ι (v j))).V=ι (oddQuotient h (I-2)))
    (hZ : (chart p (fun j => ι (v j))).Z=
      (chart p (fun j => ι (v j))).M*ι tau*ι phi*ι (ycoord (2*h+1) (I-2))) :
    Trace74Mask.value74 p (fun j => ι (v j))=0 := by
  have hn := congrArg ι (quotient_ordinate_norm I h hI)
  simp only [map_add, map_mul, map_one] at hn
  rw [output_chart,hQ,hE,hF,hV,hZ]
  linear_combination -((chart p (fun j => ι (v j))).M*ι tau*ι phi)^2*hn

#print axioms Trace74ChartAssembly.zero_of_same_orbit
end Trace74ChartAssembly
