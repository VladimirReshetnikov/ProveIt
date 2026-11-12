import NaturalRank
import MainBalance

/-! Source-only composition from the 84 graph's own zero. The Y≥8 bound,
all port casts and all-positive valuation remain explicit. No Lean result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OwnZeroMainBalance84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open NaturalRank84Draft MainBalance84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Derive the natural main norm and carrier balance without separately
assuming a natural rank representation. The Y bound remains explicit. -/
theorem norm_and_balance (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hv : ∀ j, 0<v j) (hY : 8≤AuxGraphNormClientDraft.Y beta v)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let R := naturalRank beta MC MF v
    let U := AuxGraphNormClientDraft.U beta v
    let X := AuxGraphNormClientDraft.X beta v
    let a := AuxGraphNormClientDraft.a beta v
    let c := AuxGraphNormClientDraft.c beta v
    let H : V := 3+4*a
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*c*c ∧
      U*d+H*AuxGraphNormClientDraft.k v=U*(X+a*c)+H*(U*v 12+R+1) := by
  let R := naturalRank beta MC MF v
  have hR : AuxGraphNormClientDraft.rank p beta v=ι R :=
    rank_of_84_zero p beta K MC MF v hbeta hK hMC hMF (hv 1) (hv 6) hz
  have hk : 0<AuxGraphNormClientDraft.k v := by
    dsimp [AuxGraphNormClientDraft.k]
    exact add_pos (hv 9) (hv 10)
  exact main_norm_and_balance p beta v R hbeta (hv 7) hY hk hR hz

end DiophantineConsistency.OwnZeroMainBalance84Draft

#print axioms DiophantineConsistency.OwnZeroMainBalance84Draft.norm_and_balance
