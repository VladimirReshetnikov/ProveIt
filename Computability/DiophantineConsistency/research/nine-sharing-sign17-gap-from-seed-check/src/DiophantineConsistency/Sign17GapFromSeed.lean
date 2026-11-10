import DiophantineConsistency.Sign17ConcreteGap
import DiophantineConsistency.SharingSign17Squares

/-! SOURCE-ONLY: extract the signed-gap representative from a sign17 seed zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17GapFromSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_gap (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) (hb : 0 < beta)
    (hz : InternalZero (SharingSeed17Degree96.seed p) v) :
    ∃ gap : V, ι gap = ((ι (v 13))+1)*((ι (v 13))+1)-(ι (v 17))*(ι (v 17)) := by
  have hm : SharingSeed17Degree96.row06 p ∈
      SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p := by
    simp [SharingSeed17Degree96.firstResidual, SharingSeed17Degree96.remainingResiduals]
  have hNa := (internalZero_iff _ _).mp ((SharingSign17Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  exact Sign17ConcreteRoot.exists_from_row06 p beta v hp hb hNa
end DiophantineConsistency.Sign17GapFromSeed
#print axioms DiophantineConsistency.Sign17GapFromSeed.exists_gap
