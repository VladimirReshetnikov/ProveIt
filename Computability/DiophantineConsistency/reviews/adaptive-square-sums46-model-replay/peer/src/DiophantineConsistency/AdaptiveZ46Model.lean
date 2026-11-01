import DiophantineConsistency.AdaptiveZ46Root
import DiophantineConsistency.AdaptiveZ46Norm
import DiophantineConsistency.AdaptiveZ46Extend
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveZ46Context AdaptiveZ46Zeros AdaptiveZ46Orientation AdaptiveZ46Norm AdaptiveZ46Maps AdaptiveZ46Rest AdaptiveZ46First AdaptiveZ46Root AdaptiveZ46Extend
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 47 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveNamedValues47.literal p) v) :
    ∃ r : V, v 8 ≤ r ∧ 0 < magnitude (v 24,v 25) ∧ InternalZero (literal p) (project v r) := by
  obtain ⟨t,hmag,ht⟩ := magnitude_quotient (v 24) (v 25) (v 14) (v 34) (hv 14) (norm p v hz)
  obtain ⟨r,hr,hor⟩ := orient (v 24) (v 25) (v 14) t (v 8) ht
  refine ⟨r,hr,hmag,?_⟩
  have hall := (sum_zero p oldFill v).mp (by rw [old_literal]; exact hz)
  rw [← new_literal]
  apply (sum_zero p newFill (project v r)).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    exact (first_project p v r).mp (hall 0)
  by_cases hj : i = 14
  · subst i
    exact (root_project p v r hor).mp (hall 14)
  exact (project_rest_equiv p v r i hi hj).mp (hall i)

theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 46 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
      ∀ v : Fin 47 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues47.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 47 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveNamedValues47.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    obtain ⟨r,hr,hmag,hnewzero⟩ := project_zero p old holdpos holdzero
    have hnewpos := project_pos old r holdpos hr hmag
    let shifted : Fin 46 → V := fun i => project old r i - 1
    have hs : (fun i => shifted i + 1) = project old r := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 46 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := (extend_zero p new).mpr hnewzero
    let shifted : Fin 47 → V := fun i => extend new i - 1
    have hs : (fun i => shifted i + 1) = extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
#print axioms project_zero
#print axioms shifted_no_zero_iff
end DiophantineConsistency.AdaptiveZ46Model
