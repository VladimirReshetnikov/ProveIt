import DiophantineConsistency.Sign33ForwardAllCuts
import DiophantineConsistency.Sign33CurrentCoreCuts
import DiophantineConsistency.Sign33CurrentNaturalCoreNorms

/-! Source-only candidate: source zero supplies one constructor AllCuts valuation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentForwardAllCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_has_all_cuts (ports : Fin 4 → V) (u : Fin 14 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    ∃ gap tau inner value negative : V,
      Sign33ResidualAssembly.AllCuts ports
        (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)) := by
  obtain ⟨gap,tau,inner,value,negative,hgap,htau,hinner,hvalue,hnegative⟩ :=
    Sign33CurrentCoreCuts.five_core_representatives_of_current_zero u hz
  have hnorms := Sign33CurrentNaturalCoreNorms.natural_source_core_norms u hz
  have hports : (fun j => ι (ports j)) = ModelThirteenCarrier.ringPorts (V := V) := by
    funext j
    exact (hp j).symm
  have hports2 : (fun j => ι (ports j)) = Norm38FixedPortNorms.ringPorts (V := V) := by
    funext j
    exact (hp j).symm
  apply Exists.intro gap
  apply Exists.intro tau
  apply Exists.intro inner
  apply Exists.intro value
  apply Exists.intro negative
  apply Sign33ForwardAllCuts.all_cuts_of_core ports u gap tau inner value negative
  · rw [hports]; exact hgap
  · rw [hports]; exact htau
  · rw [hports]; exact hinner
  · rw [hports]; exact hvalue
  · rw [hports]; exact hnegative
  · rw [hports2]; exact hnorms
end DiophantineConsistency.Sign33CurrentForwardAllCuts
#print axioms DiophantineConsistency.Sign33CurrentForwardAllCuts.source_has_all_cuts
