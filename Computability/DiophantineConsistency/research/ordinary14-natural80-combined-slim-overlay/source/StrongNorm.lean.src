import ZeroFields
import GraphNormClient

/-! Source-only strong norm extraction from the 84 own-zero. Imported graph
and norm clients remain unelaborated; no full calibration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.StrongNorm84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 84 and 79 strong-field expressions are identical, independently of
first-root coordinates and of the other fields. -/
theorem shared_strong (p : Fin 4 → ℤ) :
    (P84QcubeGraph.graph p).gap=(P79DirectPell.graph p).gap := by rfl

/-- Extract the ordinary strong norm from the 84 graph's own zero. Only the
beta cast is needed in this statement. -/
theorem strong_norm (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let c := AuxGraphNormClientDraft.c beta v
    let Delta := AuxGraphNormClientDraft.Delta beta v
    (v 4*c*c)*(v 4*c*c)+Delta=Delta*(v 3*v 3) := by
  have hg := (ZeroFields8485Draft.fields84 p v hz).2.2.2.1
  rw [shared_strong p] at hg
  change AuxGraphNormClientDraft.eval (P79DirectPell.graph p).gap v=0 at hg
  rw [AuxGraphNormClientDraft.strong_eval p beta v hport] at hg
  exact strong_norm_of_ring_residual _ _ _ _ hg

end DiophantineConsistency.StrongNorm84Draft

#print axioms DiophantineConsistency.StrongNorm84Draft.strong_norm
