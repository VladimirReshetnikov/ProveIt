import DiophantineConsistency.Sign33CurrentForwardAllCuts
import DiophantineConsistency.Sign33ResidualIff

/-! Source-only candidate from current natural zero to a 33-seed witness. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentSourceSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_implies_seed (ports : Fin 4 → V) (u : Fin 14 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    ∃ w : Fin 33 → V,
      InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
  obtain ⟨gap,tau,inner,value,negative,hcuts⟩ :=
    Sign33CurrentForwardAllCuts.source_has_all_cuts ports u hp hz
  let w := SharingForward33.witnessCoordinates ports u gap tau inner value negative
  refine ⟨w, ?_⟩
  exact (Sign33ResidualIff.seed_zero_iff_all_cuts CurrentWindowCarry2011.ports ports
    (Fin.cons (1 : V) w) (hp 0) (hp 1) (hp 2) (hp 3)).mpr hcuts
end DiophantineConsistency.Sign33CurrentSourceSeed
#print axioms DiophantineConsistency.Sign33CurrentSourceSeed.source_implies_seed
