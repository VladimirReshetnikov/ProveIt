import DiophantineConsistency.Sign32ForwardAssemblyAll
import DiophantineConsistency.Sign32ReverseAssemblyAll

/-! UNCOMPILED symbolic pointwise zero-set equivalence, with beta cast. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem drop_lift (beta : V) (v : Fin 33 → V) :
    Sign32CoordinateRecover.drop (Sign32Substitution00.lift beta v) = v := by
  funext j
  fin_cases j <;> simp [Sign32CoordinateRecover.drop, Sign32Substitution00.lift]

theorem pointwise (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed32Sextic.seed p) v ↔
      InternalZero (SharingSeed33.seed p) (Sign32Substitution00.lift beta v) := by
  constructor
  · exact Sign32ForwardAssembly.source32_to_source33 p beta v hp0
  · intro hz
    have h := Sign32ReverseAssembly.source33_to_source32 p beta (Sign32Substitution00.lift beta v) hp0 hz
    simpa only [drop_lift] using h
end DiophantineConsistency.Sign32SeedIff
#print axioms DiophantineConsistency.Sign32SeedIff.drop_lift
#print axioms DiophantineConsistency.Sign32SeedIff.pointwise
