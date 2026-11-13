import DiophantineConsistency.AdaptiveAQ16Transport
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums AdaptiveAQ16Maps AdaptiveAQ16Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_no_zero_iff (p : Fin 4 → ℕ) (hp : 2 ≤ p 0) :
    (∀ v : Fin 16 → V, ¬ InternalZero (positiveShift (AdaptiveAQ16Literal.literal (fun j => (p j:ℤ)))) v) ↔
      ∀ v : Fin 17 → V, ¬ InternalZero (positiveShift (AdaptiveAQ17Literal.literal (fun j => (p j:ℤ)))) v := by
  constructor
  · intro h v hz
    let old : Fin 17 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j:ℤ))) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 16 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 16 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ16Literal.literal (fun j => (p j:ℤ))) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos p hp new hnewpos
    have holdzero := extend_zero p hp new hnewpos hnewzero
    let shifted : Fin 17 → V := fun i => AdaptiveAQ16Maps.extend p new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ16Maps.extend p new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero

theorem current_no_zero_iff :
    (∀ v : Fin 16 → V, ¬ InternalZero (positiveShift (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)) v) ↔
      ∀ v : Fin 17 → V, ¬ InternalZero (positiveShift (AdaptiveAQ17Literal.literal CurrentWindowCarry2011.ports)) v := by
  have hb : 2 ≤ ArithmeticAdaptiveScaledNorms2011.currentPorts 0 := by
    have h : 2 ≤ CurrentMasks2011.beta := by
      have hr : 3 ≤ CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
      have hp : CurrentMasks2011.radix ≤ CurrentMasks2011.radix^2011 := Nat.le_self_pow (by decide) _
      unfold CurrentMasks2011.beta
      omega
    simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts,Matrix.cons_val_zero] using h
  simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts_cast] using
    (shifted_no_zero_iff (V := V) ArithmeticAdaptiveScaledNorms2011.currentPorts hb)
#print axioms shifted_no_zero_iff
#print axioms current_no_zero_iff
end DiophantineConsistency.AdaptiveAQ16
