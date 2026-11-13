import FirstIndexResidues
import Q4Rank

/-! Source-only q⁴ first-index congruence from the 84 own-zero. All draft
imports are unelaborated; no rank window or exact-index claim follows. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstIndexModQ484Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence ArithmeticAdaptiveFirstDivisibility2011
open DirectFirstRootGraphClientDraft NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first Pell index is congruent to the natural rank modulo q⁴. The
strict rank window needed to remove the modulus is not assumed or derived. -/
theorem first_index_mod_q4 (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let q := AuxGraphNormClientDraft.q beta v
    let R := naturalRank beta MC MF v
    let Q := (X beta v*Y beta v)*Y beta v
    let tau := magnitude (firstP beta v,v 8)
    let kk := k v
    ∃ n r s : V, n≤kk ∧ xcoord n (2*(Q-1)+1)=tau ∧
      2*ycoord n (2*(Q-1)+1)=kk ∧ tau=1+2*Q*r ∧ kk=2*n+4*Q*s ∧
      (2*n)%(q^4)=(R+1)%(q^4) := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  let Q := (X beta v*Y beta v)*Y beta v
  let kk := k v
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hm : 0<q^4 := pow_pos hq _
  obtain ⟨n,r,s,hn,hx,hy,hr,hk⟩ :=
    FirstIndexResidues84Draft.first_index_residues p beta v hbeta (hv 0) (hv 6) (hv 7) hport hz
  have hmag : q^4∣magnitude (R+1,kk) := by
    simpa only [q,R,kk,k,AuxGraphNormClientDraft.k] using
      Q4Rank84Draft.q4_rank p beta K MC MF v hbeta hport hK hMC hMF hv hz
  have hmod : (R+1)%(q^4)=kk%(q^4) := magnitude_mod (R+1,kk) (q^4) hm hmag
  have hmultiple : q^4∣4*Q*s := by
    refine ⟨4*(X beta v)*q^2*(v 7*v 7)*s,?_⟩
    dsimp [Q,Y,q,AuxGraphNormClientDraft.q,DirectFirstRootGraphClientDraft.q]
    ring
  have hmod' : (R+1)%(q^4)=(2*n)%(q^4) := by
    rw [hk,add_comm (2*n) (4*Q*s),mod_add_remove_left_of_dvd hmultiple hm] at hmod
    exact hmod
  exact ⟨n,r,s,hn,hx,hy,hr,hk,hmod'.symm⟩

end DiophantineConsistency.FirstIndexModQ484Draft

#print axioms DiophantineConsistency.FirstIndexModQ484Draft.first_index_mod_q4
