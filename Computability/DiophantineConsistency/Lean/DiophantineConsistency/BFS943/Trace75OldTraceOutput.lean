import DiophantineConsistency.BFS943.Trace75OldTraceMap

/-! Factored squared-trace parent zero from coherent Pell/carrier parts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75OldTraceOutput
open DiophantineConsistency.TenPositiveTrace75 Trace75OldTraceMap
variable {R : Type*} [CommRing R]

theorem old_output_zero (p : Fin 4 → R) (v : Fin 10 → R) (tau f y u I : R)
    (hE : (regs p v).E=tau*tau)
    (hf : (regs p v).F0=f*f)
    (hQ : (regs p v).Q=I*I)
    (hV : oldV p v=u)
    (hZ : oldZ p v=(regs p v).M*(tau*f*y))
    (haux : I*I*u*u+y*y=1+I*I*y*y) : oldValue p v=0 := by
  simp only [oldValue,Gn_def]
  rw [hE,hf,hQ,hV,hZ]
  linear_combination -((regs p v).M*(regs p v).M)*(tau*tau)*(f*f)*haux

#print axioms Trace75OldTraceOutput.old_output_zero
end Trace75OldTraceOutput
