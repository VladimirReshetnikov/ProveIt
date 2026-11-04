import DiophantineConsistency.Compact44.CompactConstructedRank
import DiophantineConsistency.Compact44.CompactPackingOriginResidue
import DiophantineConsistency.Compact44.CompactRankVariationRetry

/-! Rank properties for physical compact packing, with no residue premises. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactRankResidueJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ArithmeticRepunit ArithmeticPacking
open CompactConstructedRank CompactRankVariation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem properties {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K low high N s X) :
    population (rank K N s X) = 3*(590069*N)+2 ∧
      rank K N s X % 4 = 3 ∧ 2*(590069*N) < rank K N s X := by
  exact rank_properties h (CompactPackingOriginResidue.packing_origin_mod_four h)
    CompactLowModFour.low_mod_four

theorem rank_eq_window (K N s : V) (X : V → V) [𝚺₁-Function₁ X] :
    rank K N s X = windowRank K N s
      ((low+Exp.exp (590069*N)*(high+(Exp.exp (590069:V)-1)))*rep 590069 N) X := by
  rfl

#print axioms CompactRankResidueJoin.properties
#print axioms CompactRankResidueJoin.rank_eq_window
end CompactRankResidueJoin
