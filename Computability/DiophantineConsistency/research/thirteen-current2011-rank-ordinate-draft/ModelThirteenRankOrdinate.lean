import DiophantineConsistency.ModelThirteenCarrierPrelude
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The maintained zero fixes the main ordinate at its model rank. -/
theorem rank_ordinate (v : Fin 14 → V)
    (hz : InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    let w : Fin 14 → V := fun j => v j + 1
    (w 10 + w 11) * Y w + w 10 = ycoord (rank w) (X w * Y w + Y w) := by
  dsimp only
  set w : Fin 14 → V := fun j => v j + 1 with hwdef
  have hw : ∀ j, 0 < w j := fun j => lt_of_lt_of_le _root_.zero_lt_one le_add_self
  obtain ⟨hβ, hMC, hMF⟩ := ArithmeticCarrierSoundness2011.current_bounds (V := V)
  have hβ0 : (0 : V) < (CurrentMasks2011.beta : V) := lt_of_lt_of_le (by norm_num) hβ
  obtain ⟨ht, hfirst, hmain, hstrong, haux⟩ := ArithmeticCarrierSoundness2011.current_natural_equations v hz
  obtain ⟨_, _, _, _, _, _, _, _, hcR, _⟩ :=
    ArithmeticPellFirstIndex.maintained_first_indices
      (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
      (w 6) (w 7) (w 8) (w 9) (w 10) (w 11) (w 12) (w 13) hβ0 hMC hMF (hw 0) (hw 1) (hw 2) (hw 3)
      (hw 4) (hw 5) (hw 6) (hw 7) (hw 8) (hw 9) (hw 10) (hw 11) (hw 12) (hw 13)
      ht hfirst hmain hstrong haux
  change (w 10 + w 11) * Y w + w 10 = ycoord (rank w) (X w * Y w + Y w) at hcR
  exact hcR

end DiophantineConsistency.ModelThirteenCarrier
