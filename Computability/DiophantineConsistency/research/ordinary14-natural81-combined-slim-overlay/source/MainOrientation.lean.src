import SignedMainNorm
import ModifiedCarrierFacts

/-! Source-only conditional orientation. Natural rank representation and
Y≥8 are explicit; no graph rank extraction or Lean result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainOrientation84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open ModifiedCarrierFactsDraft SignedMainNorm84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Under an explicit natural representation of the signed rank, the modified
main-parts inequality orients the signed root positively. -/
theorem oriented_main_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (R : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)
    (hY : 8≤AuxGraphNormClientDraft.Y beta v)
    (hk : 0<AuxGraphNormClientDraft.k v)
    (hR : AuxGraphNormClientDraft.rank p beta v=ι R)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*
        AuxGraphNormClientDraft.c beta v*AuxGraphNormClientDraft.c beta v ∧
      AuxGraphNormClientDraft.mainValue p beta v=ι (AuxGraphNormClientDraft.U beta v*d) := by
  let q := AuxGraphNormClientDraft.q beta v
  let X := AuxGraphNormClientDraft.X beta v
  let Y := AuxGraphNormClientDraft.Y beta v
  let U := AuxGraphNormClientDraft.U beta v
  let k := AuxGraphNormClientDraft.k v
  let a := AuxGraphNormClientDraft.a beta v
  let c := AuxGraphNormClientDraft.c beta v
  let H : V := 3+4*a
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hU : 0<U := by
    dsimp [U,AuxGraphNormClientDraft.U,AuxGraphNormClientDraft.Y]
    exact mul_pos (mul_pos (mul_pos hq (mul_pos hq hq)) hs) (mul_pos hq hq)
  have hparts : H*k<U*(X+a*c)+H*(U*v 12+R+1) := by
    simpa only [H,a,c,X,Y,k] using
      modified_main_parts_positive U X Y k (v 9) (v 12) R hU hY hk
  have hlt : ι (H*k)<ι (U*(X+a*c)+H*(U*v 12+R+1)) := ι_lt_ι.mpr hparts
  have hrepr : AuxGraphNormClientDraft.mainValue p beta v =
      ι (U*(X+a*c)+H*(U*v 12+R+1))-ι (H*k) := by
    simp [AuxGraphNormClientDraft.mainValue,hR,U,X,a,c,H,k,map_add,map_mul,map_one]
    <;> ring
  have hpos : 0<AuxGraphNormClientDraft.mainValue p beta v := by
    rw [hrepr]
    exact sub_pos.mpr hlt
  obtain ⟨d,hd,hr⟩ := signed_main_root p beta v hport hs hz
  refine ⟨d,hd,?_⟩
  rcases hr with h | h
  · exact h
  · have hn : AuxGraphNormClientDraft.mainValue p beta v≤0 := by
      rw [h]
      exact neg_nonpos.mpr (ι_nonneg _)
    exact False.elim ((not_le_of_gt hpos) hn)

end DiophantineConsistency.MainOrientation84Draft

#print axioms DiophantineConsistency.MainOrientation84Draft.oriented_main_root
