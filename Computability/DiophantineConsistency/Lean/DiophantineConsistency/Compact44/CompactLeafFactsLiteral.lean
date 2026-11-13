import DiophantineConsistency.Compact44.CompactLeafFacts
import DiophantineConsistency.Compact44.FreeJGraphCongruenceExplore

/-! A positive zero of the free-J literal supplies all six leaf facts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLeafFactsLiteral
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Ordinary12FreeJ CompactLeafFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem of_literal (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : LeafFacts p v where
  indices hb hl hh := FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  transport hb := (FreeJFirstTransport.freej_first_factor_transport p v hb hv hz).2
  pairMod hb := FreeJGraphCongruenceExplore.first_pair_mod p v hb hv hz
  power hb hl hh hbeta := FreeJPowerFinish.graph_power p v hb hl hh hv hz hbeta
  projection hb hl hh := FreeJPowerProjection.graph_projection p v hb hl hh hv hz
  ydiv hJ hb := FreeJRootBinding.first_factor_forces_Y_divisible p v hz hJ hb

#print axioms CompactLeafFactsLiteral.of_literal
end CompactLeafFactsLiteral
