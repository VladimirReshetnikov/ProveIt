import DiophantineConsistency.Sign14TauBound
import DiophantineConsistency.Sign14ScalarWindow
import DiophantineConsistency.Sign14TauValue

/-! SOURCE-ONLY natural tau representative from reduced seed and explicit bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14TauLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign14SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_tau_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    ∃ tau : V, ι tau = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (v j)) := by
  have hq := Sign14ScalarWindow.q_bound_of_seed p beta K MC MF v hp0 hp1 hb hMC hMF hz
  have he := Sign14TauValue.tau_eval p beta MC MF v hp0 hp2 hp3 hq
  have ht := Sign14TauBound.tau_embedding p beta K MC MF v hp0 hp1 hb hMC hMF hz
  exact ⟨E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1)) - Sign14RankValue.Rank beta MC MF v, ht.trans he.symm⟩
end DiophantineConsistency.Sign14TauLift
#print axioms DiophantineConsistency.Sign14TauLift.exists_tau_of_seed
