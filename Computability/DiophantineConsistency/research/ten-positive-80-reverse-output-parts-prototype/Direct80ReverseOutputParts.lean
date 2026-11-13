import Direct80Graph
import ReverseCross

/-! Exact 80 output zero from coherent scalar Pell/carrier parts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80ReverseOutputParts
open DiophantineConsistency TenPositive80Graph TenPositiveReverseCross
variable {R : Type*} [CommRing R]

theorem output_zero (p : Fin 4 → ℤ) (v : Fin 10 → R) (tau f y u I : R)
    (hE : (graph p).e.evalRing v=tau*tau)
    (hf : f*f=(graph p).a.evalRing v+1)
    (hQ : (graph p).q.evalRing v=I*I)
    (hV : (graph p).v.evalRing v=u)
    (hZ : (graph p).z.evalRing v=(graph p).m.evalRing v*(tau*f*y))
    (haux : I*I*u*u+y*y=1+I*I*y*y) :
    (graph p).output.evalRing v=0 := by
  rw [output_eval,g_eval,hE,←hf,hQ,hV,hZ]
  have h := cross_zero ((graph p).m.evalRing v) tau f y u I (I*I)
    ((graph p).m.evalRing v*(tau*f*y)) rfl rfl haux
  simpa only [mul_assoc] using h

#print axioms TenPositive80ReverseOutputParts.output_zero
end TenPositive80ReverseOutputParts
