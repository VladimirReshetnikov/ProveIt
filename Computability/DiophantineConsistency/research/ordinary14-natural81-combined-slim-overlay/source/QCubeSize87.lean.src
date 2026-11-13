import FirstQuotient87
import QCubeSize

/-! Source-only Y≥8 from the 87 own-zero q³ quotient. No other graph zero,
Lean elaboration, index classification or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.QCubeSize87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive beta/J/Y and an 87 own-zero yield Y≥8 using the q³ quotient. -/
theorem Y_at_least_eight (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) : 8≤v 7 := by
  obtain ⟨s,tau,hs,hYq,_,_⟩ :=
    FirstQuotient87Draft.quotient_and_root p beta v hbeta hJ hY hport hz
  let u := Function.update v 7 s
  have hJ' : 0<u 0 := by simpa [u] using hJ
  have hs' : 0<u 7 := by simpa [u] using hs
  have hbound := QCubeSize84Draft.Y_at_least_eight beta u hbeta hJ' hs'
  have hbound' : 8≤Q beta v*s := by
    simpa [u,AuxGraphNormClientDraft.Y,AuxGraphNormClientDraft.q,Q,q] using hbound
  rw [hYq]
  exact hbound'

end DiophantineConsistency.QCubeSize87Draft

#print axioms DiophantineConsistency.QCubeSize87Draft.Y_at_least_eight
