import P72FirstInputs
import MainIndex
import StrongNorm
import AuxNorm
import DiophantineConsistency.Compact44.P72Exact

/-! Source-only exact-index composition for an 84 own-zero. Every bare
import is an unelaborated draft; provider compatibility and Lean remain open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72ExactIndices84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence ArithmeticPellHalfIndex NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed P72 exact-index application to a positive 84 graph zero, with
all port casts and symbolic mask inequalities explicit. The same main root
retains its natural carrier balance. -/
theorem exact_indices (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let q := AuxGraphNormClientDraft.q beta v
    let R := naturalRank beta MC MF v
    let U := AuxGraphNormClientDraft.U beta v
    let X := AuxGraphNormClientDraft.X beta v
    let Y := AuxGraphNormClientDraft.Y beta v
    let a := AuxGraphNormClientDraft.a beta v
    let c := AuxGraphNormClientDraft.c beta v
    let k := AuxGraphNormClientDraft.k v
    let H : V := 3+4*a
    ∃ n m d s : V, 13≤n ∧ n<m ∧ m=R ∧ 2*n=R+1 ∧
      2*ycoord n (2*((X*Y)*Y-1)+1)=k ∧ k=2*n+4*((X*Y)*Y)*s ∧
      xcoord m a=d ∧ ycoord m a=c ∧
      U*d+H*k=U*(X+a*c)+H*(U*v 12+R+1) := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  let U := AuxGraphNormClientDraft.U beta v
  let X := AuxGraphNormClientDraft.X beta v
  let Y := AuxGraphNormClientDraft.Y beta v
  let a := AuxGraphNormClientDraft.a beta v
  let c := AuxGraphNormClientDraft.c beta v
  let k := AuxGraphNormClientDraft.k v
  have hgap : v 1+v 2<q := GuardGap84Draft.gap_of_84_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hF1 : 1≤v 1 := pos_iff_one_le.mp (hv 1)
  have ha1 : 1≤v 2 := pos_iff_one_le.mp (hv 2)
  have hgap1 : v 1+v 2+1≤q := lt_iff_succ_le.mp hgap
  have hq3 : 3≤q := by nlinarith
  have hqpos : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hX : 0<X := by dsimp [X,AuxGraphNormClientDraft.X]; exact mul_pos hqpos (hv 6)
  have hYq : Y=q*(q*q)*v 7 := rfl
  have hc : c=v 9+Y*k := rfl
  have ha : a=X*Y+Y := rfl
  have hdelta : AuxGraphNormClientDraft.Delta beta v=delta a := by
    dsimp [AuxGraphNormClientDraft.Delta,delta,a]
    ring
  obtain ⟨hR26,hRwindow,n,r,s,hn,hxfirst,hny,hr,hks,hnmod⟩ :=
    P72FirstInputs84Draft.first_inputs p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  obtain ⟨d,m,hm,hx,hy,hnorm,hbal⟩ :=
    MainIndex84Draft.main_index p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz
  have hstrong := StrongNorm84Draft.strong_norm p beta v hport hz
  rw [hdelta] at hstrong
  have haux := AuxNorm84Draft.aux_norm p beta K MC MF v hport hK hMCcast hMFcast hv hz
  change 2*ycoord n (2*((X*Y)*Y-1)+1)=k at hny
  change k=2*n+4*((X*Y)*Y)*s at hks
  have hexact := P72Exact.indices_ordinary q X Y k R d c a (v 7) (v 4) (v 3) (v 5) (v 11)
    n s (q^4) m (v 9) hq3 hX (hv 7) hYq (hv 9) hc (hv 4) (hv 3) ha
    hR26 hny hks hRwindow hnmod hy hnorm hstrong haux
  exact ⟨n,m,d,s,hexact.1,hexact.2.1,hexact.2.2.1,hexact.2.2.2,
    hny,hks,hx,hy,hbal⟩

end DiophantineConsistency.P72ExactIndices84Draft

#print axioms DiophantineConsistency.P72ExactIndices84Draft.exact_indices
