import MainNormClient
import SignedScaledRoot

/-! Source-only signed 84 main root. All imported drafts are unelaborated;
no orientation, index, carrier balance or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.SignedMainNorm84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing SignedScaledRootDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- From the 84 graph's own zero, retain the exact signed scaled root.
No choice between the two signs has yet been made. -/
theorem signed_main_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*
        AuxGraphNormClientDraft.c beta v*AuxGraphNormClientDraft.c beta v ∧
      (AuxGraphNormClientDraft.mainValue p beta v=ι (AuxGraphNormClientDraft.U beta v*d) ∨
       AuxGraphNormClientDraft.mainValue p beta v= -ι (AuxGraphNormClientDraft.U beta v*d)) := by
  let q := AuxGraphNormClientDraft.q beta v
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hU : 0<AuxGraphNormClientDraft.U beta v := by
    dsimp [AuxGraphNormClientDraft.U,AuxGraphNormClientDraft.Y]
    exact mul_pos (mul_pos (mul_pos hq (mul_pos hq hq)) hs) (mul_pos hq hq)
  have hmain := (ZeroFields8485Draft.fields84 p v hz).2.1
  rw [MainNorm84Draft.shared_main p] at hmain
  change AuxGraphNormClientDraft.eval (P79DirectPell.graph p).A1 v=0 at hmain
  rw [AuxGraphNormClientDraft.main_eval p beta v hport] at hmain
  exact scaled_signed_root _ _ _ hU (sub_eq_zero.mp hmain)

end DiophantineConsistency.SignedMainNorm84Draft

#print axioms DiophantineConsistency.SignedMainNorm84Draft.signed_main_root
