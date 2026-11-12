import PositiveMainBalance
import DiophantineConsistency.ArithmeticPellClassification

/-! Source-only main Pell index with its natural carrier balance. All graph
and balance imports are unelaborated drafts; no rank equality is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.MainIndex84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open NaturalRank84Draft PositiveMainBalance84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Classify the same natural main root produced by the 84 own-zero balance.
The index is not yet identified with the graph rank. -/
theorem main_index (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let R := naturalRank beta MC MF v
    let U := AuxGraphNormClientDraft.U beta v
    let X := AuxGraphNormClientDraft.X beta v
    let a := AuxGraphNormClientDraft.a beta v
    let c := AuxGraphNormClientDraft.c beta v
    let H : V := 3+4*a
    ∃ d m : V, m≤c ∧ xcoord m a=d ∧ ycoord m a=c ∧
      d*d=1+delta a*c*c ∧
      U*d+H*AuxGraphNormClientDraft.k v=U*(X+a*c)+H*(U*v 12+R+1) := by
  let a := AuxGraphNormClientDraft.a beta v
  let c := AuxGraphNormClientDraft.c beta v
  obtain ⟨d,hn,hbal⟩ := PositiveMainBalance84Draft.norm_and_balance
    p beta K MC MF v hbeta hport hK hMC hMF hv hz
  have hdelta : AuxGraphNormClientDraft.Delta beta v=delta a := by
    dsimp [AuxGraphNormClientDraft.Delta,delta,a]
    ring
  have hnorm : d*d=1+delta a*c*c := by
    rw [←hdelta]
    exact hn
  obtain ⟨m,hm,hx,hy⟩ := ArithmeticPellClassification.solution_index a d c hnorm
  exact ⟨d,m,hm,hx,hy,hnorm,hbal⟩

end DiophantineConsistency.MainIndex84Draft

#print axioms DiophantineConsistency.MainIndex84Draft.main_index
