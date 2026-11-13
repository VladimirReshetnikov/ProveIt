import NaturalRank
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Source-only 84 own-zero scalar rank window. Explicit mask bounds remain;
no compact-port application or exact Pell-index claim is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RankWindow84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing GuardGap84Draft NaturalRank84Draft
open ArithmeticAdaptiveRankWindow2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Apply the scalar rank window to the natural rank from an 84 own-zero.
The mask inequalities are explicit and need a separate port instantiation. -/
theorem rank_window (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let q := AuxGraphNormClientDraft.q beta v
    let R := naturalRank beta MC MF v
    24≤R ∧ R+q^3+q+1≤q^4 ∧ R+1<q^4 := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  have hgap : v 1+v 2<q := gap_of_84_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hq : q=beta*v 0+1 := by dsimp [q,AuxGraphNormClientDraft.q]; ring
  have hqm : q-1=v 0*beta := by
    have h : q=v 0*beta+1 := by dsimp [q,AuxGraphNormClientDraft.q]; ring
    rw [h,add_tsub_cancel_right]
  have hrepr : R=((q-1)*(q-v 1)+v 2)*(q^2-1)+(MC+q*MF)*v 0 := by
    change (v 2+(q-v 1)*(v 0*beta))*(q*q-1)+v 0*(MC+MF*q)=_
    rw [hqm,pow_two]
    ring
  have hwin := scalar_rank_window q beta MC MF (v 0) (v 1) (v 2)
    hbeta (hv 0) (hv 1) (hv 2) hMC hMF hq hgap
  rw [←hrepr] at hwin
  have hqpos : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hp : 0<q^3 := pow_pos hqpos _
  refine ⟨hwin.1,hwin.2,?_⟩
  have hlt : R+1<R+q^3+q+1 := by nlinarith
  exact lt_of_lt_of_le hlt hwin.2

end DiophantineConsistency.RankWindow84Draft

#print axioms DiophantineConsistency.RankWindow84Draft.rank_window
