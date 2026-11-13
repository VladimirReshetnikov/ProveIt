import Trace74CarrierChartBinding

/-! Bind the negative-rank CRT residues to one actual updated chart tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Trace74NegativeRankTuple
open Trace74ChartAssembly Trace74CarrierChartBinding
variable {R : Type*} [CommRing R]

/-- Updating the F and C coordinates realizes the negative-rank chart on
the same tuple. The two CRT divisibilities and `H ∣ K` remain premises. -/
theorem updated_carrier (p : Fin 4 → R) (v : Fin 10 → R) (N : R)
    (hB : let h := p 0*v 0; let q := h+1; let C := q*h+N;
      h ∣ (p 1+v 5)*C-1)
    (he : let h := p 0*v 0; let q := h+1; let X := v 5*q;
      let Y := (q*q*q)*v 6; let k := v 8+v 9;
      let RJ := (p 2+q*p 3)*v 0; let rank := RJ-(q*q-1)*N;
      X*Y ∣ k-rank-1)
    (hK : let q := p 0*v 0+1; let X := v 5*q; let Y := (q*q*q)*v 6;
      let c := (v 8+v 9)*Y+v 8; let H := 4*(X*Y+Y)-1;
      H ∣ X*(3*c-2*X)+2) :
    let q := p 0*v 0+1
    let w := Function.update (Function.update v 1 1) 2 (q*(p 0*v 0)+N)
    (chart p w).M ∣ (chart p w).Z := by
  let q := p 0*v 0+1
  let w := Function.update (Function.update v 1 1) 2 (q*(p 0*v 0)+N)
  change (chart p w).M ∣ (chart p w).Z
  apply actual_carrier_divisibility p w
  · simpa [w,q] using hB
  · convert he using 1 <;> simp [w,q] <;> ring_nf
  · simpa [w,q] using hK

#print axioms Trace74NegativeRankTuple.updated_carrier
end Trace74NegativeRankTuple
