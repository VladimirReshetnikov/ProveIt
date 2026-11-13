import FirstNormClient
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Source-only first-index residue extraction from the 84 own-zero. Draft
imports are unelaborated; no rank identification or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstIndexResidues84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence DirectFirstRootGraphClientDraft FirstNorm84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A first-index witness and its two natural residue quotients from the 84
own-zero. The rank relationship remains a separate obligation. -/
theorem first_index_residues (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let Q := (X beta v*Y beta v)*Y beta v
    let tau := magnitude (firstP beta v,v 8)
    let K := k v
    ∃ n r s : V, n≤K ∧ xcoord n (2*(Q-1)+1)=tau ∧
      2*ycoord n (2*(Q-1)+1)=K ∧ tau=1+2*Q*r ∧ K=2*n+4*Q*s := by
  let Q := (X beta v*Y beta v)*Y beta v
  let tau := magnitude (firstP beta v,v 8)
  let K := k v
  have hq : 0<q beta v := by dsimp [q]; simp
  have hX : 0<X beta v := by dsimp [X]; exact mul_pos hq hw
  have hY : 0<Y beta v := by dsimp [Y]; exact mul_pos (mul_pos hq (mul_pos hq hq)) hs
  have hQ : 0<Q := by dsimp [Q]; exact mul_pos (mul_pos hX hY) hY
  have hQ1 : 1≤Q := pos_iff_one_le.mp hQ
  have he : Q-1+1=Q := tsub_add_cancel_of_le hQ1
  have hn := (first_norm p beta v hbeta hJ hport hz).2
  have hnorm : tau*tau=1+Q*(Q+1)*K*K := by
    rw [hn]
    dsimp [tau,Q,K,radicand,firstP,ell]
    ring
  have hd : ArithmeticPellFirstNorm.discriminant (Q-1)=Q*(Q+1) := by
    unfold ArithmeticPellFirstNorm.discriminant
    rw [show Q-1+2=(Q-1+1)+1 by ring,he]
  have hdisc : tau*tau=1+ArithmeticPellFirstNorm.discriminant (Q-1)*K*K := by
    rw [hd]
    exact hnorm
  obtain ⟨n,r,s,hnk,hx,hy,hr,hk⟩ := ArithmeticPellFirstNorm.solution_residues (Q-1) tau K hdisc
  have hr' : tau=1+2*Q*r := by simpa only [he] using hr
  have hk' : K=2*n+4*Q*s := by simpa only [he] using hk
  exact ⟨n,r,s,hnk,hx,hy,hr',hk'⟩

end DiophantineConsistency.FirstIndexResidues84Draft

#print axioms DiophantineConsistency.FirstIndexResidues84Draft.first_index_residues
