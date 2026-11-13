import PositiveMainBalance
import ModifiedCarrierFacts

/-! Source-only q⁴ rank congruence from the 84 own-zero. Imported drafts are
unelaborated; no rank window or exact-index conclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Q4Rank84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open NaturalRank84Draft ModifiedCarrierFactsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The natural balance of the positive 84 own-zero gives q⁴ dividing the
signed magnitude of R+1−k. The factor-three cancellation is valid even
when q is divisible by three. -/
theorem q4_rank (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let q := AuxGraphNormClientDraft.q beta v
    let R := naturalRank beta MC MF v
    q^4∣magnitude (R+1,AuxGraphNormClientDraft.k v) := by
  let q := AuxGraphNormClientDraft.q beta v
  let X := AuxGraphNormClientDraft.X beta v
  let Y := AuxGraphNormClientDraft.Y beta v
  let U := AuxGraphNormClientDraft.U beta v
  let a := AuxGraphNormClientDraft.a beta v
  let c := AuxGraphNormClientDraft.c beta v
  let k := AuxGraphNormClientDraft.k v
  let R := naturalRank beta MC MF v
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hY : q^3∣Y := by
    refine ⟨v 7,?_⟩
    dsimp [Y,AuxGraphNormClientDraft.Y]
    ring
  have hU : U=q^5*v 7 := by
    dsimp [U,Y,AuxGraphNormClientDraft.U,AuxGraphNormClientDraft.Y]
    ring
  obtain ⟨d,_,hbal⟩ := PositiveMainBalance84Draft.norm_and_balance
    p beta K MC MF v hbeta hport hK hMC hMF hv hz
  have hbal' : U*d+(3+4*Y*(X+1))*k =
      U*(X+a*c)+(3+4*Y*(X+1))*(U*v 12+R+1) := by
    convert hbal using 1 <;> dsimp [a,AuxGraphNormClientDraft.a] <;> ring
  exact q4_from_modified_balance q Y X R k U (v 7) (X+a*c) d (v 12)
    hq hY hU hbal'

end DiophantineConsistency.Q4Rank84Draft

#print axioms DiophantineConsistency.Q4Rank84Draft.q4_rank
