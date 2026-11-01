import DiophantineConsistency.AdaptiveAQ31
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ31ConditionalNoZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An existence-preserving orientation suffices; individual zeros need not orient. -/
theorem shifted_no_zero_iff_of_orient (p : Fin 4 → ℤ)
    (horient : (∃ v : Fin 32 → V, (∀ i, 0 < v i) ∧
        InternalZero (AdaptiveAQ32Literal.literal p) v) →
      ∃ v : Fin 32 → V, (∀ i, 0 < v i) ∧ v 24 < v 23 ∧
        InternalZero (AdaptiveAQ32Literal.literal p) v) :
    (∀ v : Fin 31 → V, ¬ InternalZero (positiveShift (AdaptiveAQ31Literal.literal p)) v) ↔
      ∀ v : Fin 32 → V, ¬ InternalZero (positiveShift (AdaptiveAQ32Literal.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 32 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ32Literal.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    obtain ⟨w, hw, hlt, hwzero⟩ := horient ⟨old, holdpos, holdzero⟩
    obtain ⟨new, hnewpos, hnewzero⟩ := (AdaptiveAQ31.oriented_exists_iff p).mp ⟨w, hw, hlt, hwzero⟩
    let shifted : Fin 31 → V := fun i => new i - 1
    have hs : (fun i => shifted i + 1) = new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 31 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ31Literal.literal p) new :=
      (internalZero_positiveShift _ _).mp hz
    obtain ⟨old, holdpos, _, holdzero⟩ := (AdaptiveAQ31.oriented_exists_iff p).mpr ⟨new, hnewpos, hnewzero⟩
    let shifted : Fin 32 → V := fun i => old i - 1
    have hs : (fun i => shifted i + 1) = old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
#print axioms shifted_no_zero_iff_of_orient
end DiophantineConsistency.AdaptiveAQ31ConditionalNoZero
