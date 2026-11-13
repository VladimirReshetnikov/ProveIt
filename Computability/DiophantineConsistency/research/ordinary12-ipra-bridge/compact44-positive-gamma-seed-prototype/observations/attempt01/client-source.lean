import CompactRankResidueJoin
import DiophantineConsistency.ArithmeticAdaptiveConstructionCorrectionSeed2011

/-! The actual compact outer seed and calibrated transport produce the
positive adaptive gamma, for the *same* supplied seed witnesses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPositiveGammaSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPacking ArithmeticOuterSeed
open ArithmeticAdaptiveConstructionCorrectionSeed2011
open CompactConstructedRank CompactRankResidueJoin
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_gamma {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (hpack : PackingInput 590069 K low high N s X)
    (sY n eta zeta gammaOld w : V)
    (hsY : 0<sY) (hgammaOld : 0<gammaOld)
    (hseed : SeedRelations (590069*N) (rank K N s X) sY n eta zeta gammaOld)
    (hXq : Exp.exp (rank K N s X) = Exp.exp (590069*N)*w) :
    ∃ t gamma : V, 0<gamma ∧
      eta+zeta=rank K N s X+1+
        ((sY*(Exp.exp (590069*N))^3)*(Exp.exp (590069*N))^2)*t ∧
      gamma+w=gammaOld+t := by
  exact positive_correction_of_seed (590069*N) (rank K N s X) sY n eta zeta gammaOld w
    hsY hgammaOld (properties hpack).2.1 hXq hseed

#print axioms CompactPositiveGammaSeed.positive_gamma
end CompactPositiveGammaSeed
