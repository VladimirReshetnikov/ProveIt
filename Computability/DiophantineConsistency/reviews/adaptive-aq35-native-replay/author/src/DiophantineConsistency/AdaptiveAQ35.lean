import DiophantineConsistency.AdaptiveAQ35Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ35
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14
open AdaptiveAQ35Context AdaptiveAQ35Zeros AdaptiveAQ35Positive AdaptiveAQ35Maps AdaptiveAQ35Transport AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 36 → V)
    (hz : InternalZero (AdaptiveAQ36Literal.literal p) v) :
    InternalZero (AdaptiveAQ35Literal.literal p) (project v) := by
  have ho : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have hall := old_all p oldFill v ho
  have hin := project_inputs p v hz
  rw [← AdaptiveAQ35Literal.new_literal]
  apply (new_zero p newFill (project v)).mpr
  constructor
  · have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p 0) oldFill newFill v (project v) hin)
    exact eqv.mp (hall 0)
  · intro i
    have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p (tailIndex i)) oldFill newFill v (project v) hin)
    exact eqv.mp (hall (tailIndex i))

theorem removed_zero (p : Fin 4 → ℤ) (v : Fin 35 → V) :
    InternalZero ((residuals p 4).subst newFill) v := by
  change InternalZero ((newFill (.inl ())) - (newFill (.inl ()))) v
  exact (sub_zero_iff_equiv _ _ v).mpr (equivalent_refl _)

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 35 → V)
    (hz : InternalZero (AdaptiveAQ35Literal.literal p) v) :
    InternalZero (AdaptiveAQ36Literal.literal p) (extend v) := by
  have hn : InternalZero ((newSum p).subst newFill) v := by rw [AdaptiveAQ35Literal.new_literal]; exact hz
  obtain ⟨h0,ht⟩ := (new_zero p newFill v).mp hn
  have hin := extend_inputs v
  have htrans (i : Fin 23) (h : InternalZero ((residuals p i).subst newFill) v) :
      InternalZero ((residuals p i).subst oldFill) (extend v) := by
    exact (equivalent_zero_iff (subst_equiv_hetero (residuals p i) oldFill newFill (extend v) v hin)).mpr h
  rw [← old_literal]
  apply (old_zero p oldFill (extend v)).mpr
  constructor
  · exact htrans 0 h0
  · intro i
    by_cases h4 : i.succ = 4
    · apply htrans
      rw [h4]
      exact removed_zero p v
    · obtain ⟨j,hj⟩ := tail_covers i.succ (by simp) h4
      apply htrans
      simpa only [hj] using ht j

theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 35 → V, ¬ InternalZero (positiveShift (AdaptiveAQ35Literal.literal p)) v) ↔
      ∀ v : Fin 36 → V, ¬ InternalZero (positiveShift (AdaptiveAQ36Literal.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 36 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ36Literal.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 35 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 35 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ35Literal.literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos p new hnewpos hnewzero
    have holdzero := extend_zero p new hnewzero
    let shifted : Fin 36 → V := fun i => AdaptiveAQ35Maps.extend new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ35Maps.extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
#print axioms project_zero
#print axioms removed_zero
#print axioms extend_zero
#print axioms shifted_no_zero_iff
end DiophantineConsistency.AdaptiveAQ35
