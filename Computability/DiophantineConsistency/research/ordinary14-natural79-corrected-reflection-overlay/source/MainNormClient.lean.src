import ZeroFields
import GraphNormClient

/-! Source-only 84 main-norm extraction via the shared 79 main field.
All bare imports are unelaborated drafts; no orientation/index claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainNorm84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal modified main field has the same expression DAG in the
84 and 79 drafts. This is not a claim about their first fields or outputs. -/
theorem shared_main (p : Fin 4 → ℤ) :
    (P84QcubeGraph.graph p).A1=(P79DirectPell.graph p).A1 := by rfl

/-- The actual 84 graph zero yields an unsigned natural main norm root.
The beta cast and the positivity of the s coordinate are explicit. No
orientation, Pell index, natural rank, or carrier balance is concluded. -/
theorem natural_main_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*
      AuxGraphNormClientDraft.c beta v*AuxGraphNormClientDraft.c beta v := by
  let q := AuxGraphNormClientDraft.q beta v
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hU : 0<AuxGraphNormClientDraft.U beta v := by
    dsimp [AuxGraphNormClientDraft.U,AuxGraphNormClientDraft.Y]
    exact mul_pos (mul_pos (mul_pos hq (mul_pos hq hq)) hs) (mul_pos hq hq)
  have hmain := (ZeroFields8485Draft.fields84 p v hz).2.1
  rw [shared_main p] at hmain
  change AuxGraphNormClientDraft.eval (P79DirectPell.graph p).A1 v=0 at hmain
  rw [AuxGraphNormClientDraft.main_eval p beta v hport] at hmain
  have hsq := sub_eq_zero.mp hmain
  exact root_of_scaled_ring_square _ _ _ hU hsq

end DiophantineConsistency.MainNorm84Draft

#print axioms DiophantineConsistency.MainNorm84Draft.shared_main
#print axioms DiophantineConsistency.MainNorm84Draft.natural_main_root
