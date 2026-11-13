import DiophantineConsistency.AdaptiveAQ27Transport
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ27
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveDirectOrdinateSquareSums AdaptiveAQ27Maps AdaptiveAQ27Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 27 → V, ¬ InternalZero (positiveShift (AdaptiveAQ27Literal.literal p)) v) ↔
      ∀ v : Fin 28 → V, ¬ InternalZero (positiveShift (AdaptiveAQ28Literal.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 28 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ28Literal.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 27 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 27 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ27Literal.literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := extend_zero p new hnewzero
    let shifted : Fin 28 → V := fun i => AdaptiveAQ27Maps.extend new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ27Maps.extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero

theorem current_no_zero_iff :
    (∀ v : Fin 27 → V, ¬ InternalZero (positiveShift (AdaptiveAQ27Literal.literal CurrentWindowCarry2011.ports)) v) ↔
      ∀ v : Fin 28 → V, ¬ InternalZero (positiveShift (AdaptiveAQ28Literal.literal CurrentWindowCarry2011.ports)) v := by
  exact shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports
#print axioms shifted_no_zero_iff
#print axioms current_no_zero_iff
end DiophantineConsistency.AdaptiveAQ27
