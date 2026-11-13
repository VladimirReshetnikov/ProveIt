import Trace74RankCarrierCRT
import Trace74ChartAssembly

/-! Direct binding of carrier divisibility to the actual 74 chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CarrierChartBinding
open Trace74RankCarrierCRT Trace74ChartAssembly

variable {R : Type*} [CommRing R]

/-- The three sufficient divisibilities refer to the very same chart
tuple; `M` divides `Z` without assuming a zero or a coprimality. -/
theorem actual_carrier_divisibility (p : Fin 4 → R) (v : Fin 10 → R)
    (hB : let B := (p 1+v 5)*v 2-v 1;
      p 0*v 0 ∣ B)
    (he : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let k := v 8+v 9; let G := q*(q-v 1)-v 2;
      let rank := G*(q*q-1)+(p 2+q*p 3)*v 0;
      X*Y ∣ k-rank-1)
    (hK : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let c := (v 8+v 9)*Y+v 8; let H := 4*(X*Y+Y)-1;
      H ∣ X*(3*c-2*X)+2) :
    (chart p v).M ∣ (chart p v).Z := by
  simpa only [chart, pow_two] using carrier_divisibility (p 0*v 0) ((v 5*(p 0*v 0+1))*
    (((p 0*v 0+1)*(p 0*v 0+1)*(p 0*v 0+1))*v 6))
    (4*((v 5*(p 0*v 0+1))*(((p 0*v 0+1)*(p 0*v 0+1)*(p 0*v 0+1))*v 6)+
      (((p 0*v 0+1)*(p 0*v 0+1)*(p 0*v 0+1))*v 6))-1)
    ((p 1+v 5)*v 2-v 1)
    (v 8+v 9-(((p 0*v 0+1)*((p 0*v 0+1)-v 1)-v 2)*
      ((p 0*v 0+1)*(p 0*v 0+1)-1)+(p 2+(p 0*v 0+1)*p 3)*v 0)-1)
    ((v 5*(p 0*v 0+1))*(3*((v 8+v 9)*
      (((p 0*v 0+1)*(p 0*v 0+1)*(p 0*v 0+1))*v 6)+v 8)-
      2*(v 5*(p 0*v 0+1)))+2)
    ((chart p v).V) (v 7) hB he hK

#print axioms Trace74CarrierChartBinding.actual_carrier_divisibility
end Trace74CarrierChartBinding
