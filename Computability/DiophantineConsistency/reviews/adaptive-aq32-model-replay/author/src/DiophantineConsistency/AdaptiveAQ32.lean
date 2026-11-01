import DiophantineConsistency.AdaptiveAQ32Transport
import DiophantineConsistency.AdaptiveAQ32Positive
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ32
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14
open AdaptiveAQ32Context AdaptiveAQ32Literal AdaptiveAQ32Maps AdaptiveAQ32Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_no_zero_iff (p : Fin 4 → ℕ) (hb : (2:V) ≤ (p 0:V)) :
    (∀ v : Fin 32 → V, ¬ InternalZero (positiveShift (AdaptiveAQ32Literal.literal (fun j => (p j:ℤ)))) v) ↔
      ∀ v : Fin 33 → V, ¬ InternalZero (positiveShift (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ)))) v := by
  constructor
  · intro h v hz
    let old : Fin 33 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ))) old :=
      (internalZero_positiveShift _ _).mp hz
    have hlt := AdaptiveAQ32Positive.signed_d_positive p old hb holdpos holdzero
    have hnewpos := project_pos old holdpos hlt
    have hnewzero := project_zero (fun j => (p j:ℤ)) old hlt holdzero
    let shifted : Fin 32 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 32 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ32Literal.literal (fun j => (p j:ℤ))) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := (extend_zero (fun j => (p j:ℤ)) new).mpr hnewzero
    let shifted : Fin 33 → V := fun i => AdaptiveAQ32Maps.extend new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ32Maps.extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero

theorem current_no_zero_iff :
    (∀ v : Fin 32 → V, ¬ InternalZero (positiveShift (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports)) v) ↔
      ∀ v : Fin 33 → V, ¬ InternalZero (positiveShift (AdaptiveAQ33Literal.literal CurrentWindowCarry2011.ports)) v := by
  have hbn : 2 ≤ CurrentMasks2011.beta := le_trans (by decide) ArithmeticAdaptiveRankWindow2011.current_bounds_nat.1
  have hbv : (2:V) ≤ (CurrentMasks2011.beta:V) := by exact_mod_cast hbn
  have hb : (2:V) ≤ (ArithmeticAdaptiveScaledNorms2011.currentPorts 0:V) := by
    simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts, Matrix.cons_val_zero] using hbv
  simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts_cast] using
    (shifted_no_zero_iff (V := V) ArithmeticAdaptiveScaledNorms2011.currentPorts hb)
#print axioms shifted_no_zero_iff
#print axioms current_no_zero_iff
end DiophantineConsistency.AdaptiveAQ32
