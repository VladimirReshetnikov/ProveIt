import DiophantineConsistency.AdaptiveAQ22Transport
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ22
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums AdaptiveAQ22Maps AdaptiveAQ22Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_no_zero_iff (p : Fin 4 → ℕ) :
    (∀ v : Fin 22 → V, ¬ InternalZero (positiveShift (AdaptiveAQ22Literal.literal (fun j => (p j:ℤ)))) v) ↔
      ∀ v : Fin 26 → V, ¬ InternalZero (positiveShift (AdaptiveAQ26Literal.literal (fun j => (p j:ℤ)))) v := by
  constructor
  · intro h v hz
    let old : Fin 26 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ26Literal.literal (fun j => (p j:ℤ))) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 22 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 22 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j:ℤ))) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos p new hnewpos
    have holdzero := extend_zero p new hnewzero
    let shifted : Fin 26 → V := fun i => AdaptiveAQ22Maps.extend p new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ22Maps.extend p new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero

theorem current_no_zero_iff :
    (∀ v : Fin 22 → V, ¬ InternalZero (positiveShift (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports)) v) ↔
      ∀ v : Fin 26 → V, ¬ InternalZero (positiveShift (AdaptiveAQ26Literal.literal CurrentWindowCarry2011.ports)) v := by
  simpa only [ArithmeticAdaptiveScaledNorms2011.currentPorts_cast] using
    (shifted_no_zero_iff (V := V) ArithmeticAdaptiveScaledNorms2011.currentPorts)
#print axioms shifted_no_zero_iff
#print axioms current_no_zero_iff
end DiophantineConsistency.AdaptiveAQ22
