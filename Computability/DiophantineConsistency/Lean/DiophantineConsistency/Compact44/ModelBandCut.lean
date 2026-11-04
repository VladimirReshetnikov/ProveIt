import DiophantineConsistency.Compact44.TwoBand
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBandCut
open DiophantineConsistency CompactPartialBandRotation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_congruence_to_bands (pos : Fin 41 → ℕ) (K n q P C w F : V)
    (hn : 0<n) (hP : 0<P) (hqdef : q=1+P) (hqexp : q=Exp.exp (67*n))
    (hK : K=kernelBand pos 4393+kernelBand pos 5495+TwoBand.bareKernel)
    (hg : ((K+w)*C)%P=F) :
    ((rotatedBand pos 4393 n C+rotatedBand pos 5495 n C+TwoBand.bareRotated n C)+w*C)
      %(Exp.exp (67*n)-1)=F := by
  have hm : Exp.exp (67*n)-1=P := by
    rw [← hqexp, hqdef, add_comm, add_tsub_cancel_right]
  apply TwoBand.combined_congr pos K n C w F hn
  · rw [hm]; exact hP
  · exact hK
  · rw [hm]; exact hg
#print axioms ModelBandCut.graph_congruence_to_bands
end ModelBandCut
