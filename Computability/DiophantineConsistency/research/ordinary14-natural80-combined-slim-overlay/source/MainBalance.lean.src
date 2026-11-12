import MainOrientation

/-! Source-only extraction of the natural carrier balance under explicit
rank and size hypotheses. All imports are unelaborated drafts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainBalance84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing MainOrientation84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- From the 84 graph's own zero and an explicit natural rank representation,
produce both the natural main norm and subtraction-free carrier balance. -/
theorem main_norm_and_balance (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (R : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hs : 0<v 7)
    (hY : 8≤AuxGraphNormClientDraft.Y beta v)
    (hk : 0<AuxGraphNormClientDraft.k v)
    (hR : AuxGraphNormClientDraft.rank p beta v=ι R)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let U := AuxGraphNormClientDraft.U beta v
    let X := AuxGraphNormClientDraft.X beta v
    let a := AuxGraphNormClientDraft.a beta v
    let c := AuxGraphNormClientDraft.c beta v
    let H : V := 3+4*a
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*c*c ∧
      U*d+H*AuxGraphNormClientDraft.k v=U*(X+a*c)+H*(U*v 12+R+1) := by
  obtain ⟨d,hn,hr⟩ := oriented_main_root p beta v R hport hs hY hk hR hz
  refine ⟨d,hn,?_⟩
  have hroot : ι (AuxGraphNormClientDraft.U beta v)*ι d =
      AuxGraphNormClientDraft.mainValue p beta v := by
    simpa only [map_mul] using hr.symm
  apply ι_injective
  simp only [map_add,map_mul,map_one]
  rw [hroot]
  simp [AuxGraphNormClientDraft.mainValue,hR,AuxGraphNormClientDraft.U,
    AuxGraphNormClientDraft.X,AuxGraphNormClientDraft.a,AuxGraphNormClientDraft.c,
    AuxGraphNormClientDraft.k,map_add,map_mul,map_one]
  <;> ring

end DiophantineConsistency.MainBalance84Draft

#print axioms DiophantineConsistency.MainBalance84Draft.main_norm_and_balance
