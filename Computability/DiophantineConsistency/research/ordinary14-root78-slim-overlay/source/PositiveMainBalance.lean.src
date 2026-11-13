import OwnZeroMainBalance
import QCubeSize

/-! Source-only all-positive composition. Imports remain unelaborated drafts;
Pell indices, provider and endpoint obligations remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PositiveMainBalance84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open NaturalRank84Draft OwnZeroMainBalance84Draft QCubeSize84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An 84 own-zero with positive valuation and beta, plus the explicit port
casts, has a natural main norm and subtraction-free balance. -/
theorem norm_and_balance (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
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
    ∃ d : V, d*d=1+AuxGraphNormClientDraft.Delta beta v*c*c ∧
      U*d+H*AuxGraphNormClientDraft.k v=U*(X+a*c)+H*(U*v 12+R+1) := by
  have hY : 8≤AuxGraphNormClientDraft.Y beta v := Y_at_least_eight beta v hbeta (hv 0) (hv 7)
  exact OwnZeroMainBalance84Draft.norm_and_balance p beta K MC MF v hport hK hMC hMF hv hY hz

end DiophantineConsistency.PositiveMainBalance84Draft

#print axioms DiophantineConsistency.PositiveMainBalance84Draft.norm_and_balance
