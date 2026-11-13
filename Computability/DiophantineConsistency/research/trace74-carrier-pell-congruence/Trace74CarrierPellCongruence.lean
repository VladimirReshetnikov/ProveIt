import Trace74CarrierChartBinding

/-! An abstract Pell congruence gives the remaining carrier factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CarrierPellCongruence
open Trace74ChartAssembly Trace74CarrierChartBinding
variable {R : Type*} [CommRing R]

/-- The Pell norm and an abscissa congruence imply `H ∣ K`. This is an
all-ring implication; it does not establish the abscissa congruence. -/
theorem pell_congruence_carrier (a H X c x : R)
    (hH : H=4*a+3)
    (hnorm : x*x=1+(a*a+H)*c*c)
    (hx : H ∣ x-X-a*c) :
    H ∣ X*(3*c-2*X)+2 := by
  obtain ⟨t,ht⟩ := hx
  have hxt : x=X+a*c+H*t := by linear_combination ht
  rw [hxt] at hnorm
  have hp : H ∣ X*X+2*a*X*c-1 := by
    refine ⟨c*c-t*(2*(X+a*c)+H*t), ?_⟩
    linear_combination hnorm
  obtain ⟨s,hs⟩ := hp
  refine ⟨X*c-2*s, ?_⟩
  linear_combination -(X*c)*hH-2*hs

/-- Same-tuple chart version: the Pell abscissa condition supplies the
third premise of actual carrier divisibility. -/
theorem actual_carrier_of_pell (p : Fin 4 → R) (v : Fin 10 → R) (x : R)
    (hB : p 0*v 0 ∣ (p 1+v 5)*v 2-v 1)
    (he : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let k := v 8+v 9; let G := q*(q-v 1)-v 2;
      let rank := G*(q*q-1)+(p 2+q*p 3)*v 0;
      X*Y ∣ k-rank-1)
    (hx : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let A := X*Y+Y; let c := (v 8+v 9)*Y+v 8; let H := 4*A-1;
      H ∣ x-X-(A-1)*c)
    (hnorm : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let A := X*Y+Y; let c := (v 8+v 9)*Y+v 8;
      x*x=1+A*(A+2)*c*c) :
    (chart p v).M ∣ (chart p v).Z := by
  apply actual_carrier_divisibility p v hB he
  let q := p 0*v 0+1
  let X := v 5*q
  let Y := (q*q*q)*v 6
  let A := X*Y+Y
  let c := (v 8+v 9)*Y+v 8
  let H := 4*A-1
  change H ∣ X*(3*c-2*X)+2
  change H ∣ x-X-(A-1)*c at hx
  change x*x=1+A*(A+2)*c*c at hnorm
  have hh : H=4*(A-1)+3 := by dsimp [H]; ring
  have hn : x*x=1+((A-1)*(A-1)+H)*c*c := by
    rw [hnorm]
    dsimp [H]
    ring
  exact pell_congruence_carrier (A-1) H X c x hh hn hx

#print axioms Trace74CarrierPellCongruence.pell_congruence_carrier
#print axioms Trace74CarrierPellCongruence.actual_carrier_of_pell
end Trace74CarrierPellCongruence
