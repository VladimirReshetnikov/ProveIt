import DiophantineConsistency.AdaptiveAQ36Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ36
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14
open AdaptiveAQ36Context AdaptiveAQ36Maps AdaptiveAQ36Zeros AdaptiveAQ36Transport AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 40 → V)
    (hz : InternalZero (AdaptiveAQ40Literal.literal p) v) :
    InternalZero (AdaptiveAQ36Literal.literal p) (project v) := by
  have ho : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have hall := old_all p oldFill v ho
  have hin := project_inputs p v hz
  rw [← AdaptiveAQ36Literal.new_literal]
  apply (new_zero p (newFill p) (project v)).mpr
  constructor
  · have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p 0) oldFill (newFill p) v (project v) hin)
    exact eqv.mp (hall 0)
  · intro i
    have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p (tailIndex i)) oldFill (newFill p) v (project v) hin)
    exact eqv.mp (hall (tailIndex i))

theorem removed_zero (p : Fin 4 → ℤ) (v : Fin 36 → V) (i : Fin 4) :
    InternalZero ((residuals p (![11,12,21,25] i)).subst (newFill p)) v := by
  fin_cases i
  · change InternalZero ((newFill p (.inl 0)) - (newFill p (.inl 0))) v
    exact (sub_zero_iff_equiv _ _ v).mpr (equivalent_refl _)
  · change InternalZero ((newFill p (.inl 1)) - (newFill p (.inl 1))) v
    exact (sub_zero_iff_equiv _ _ v).mpr (equivalent_refl _)
  · change InternalZero ((newFill p (.inl 2)) - (newFill p (.inl 2))) v
    exact (sub_zero_iff_equiv _ _ v).mpr (equivalent_refl _)
  · change InternalZero ((newFill p (.inl 3)) - (newFill p (.inl 3))) v
    exact (sub_zero_iff_equiv _ _ v).mpr (equivalent_refl _)

theorem extend_zero (p : Fin 4 → ℤ) (b : ℕ) (hb : p 0 = (b : ℤ)) (v : Fin 36 → V)
    (hz : InternalZero (AdaptiveAQ36Literal.literal p) v) :
    InternalZero (AdaptiveAQ40Literal.literal p) (extend b v) := by
  have hn : InternalZero ((newSum p).subst (newFill p)) v := by rw [AdaptiveAQ36Literal.new_literal]; exact hz
  obtain ⟨h0,ht⟩ := (new_zero p (newFill p) v).mp hn
  have hin := extend_inputs p b hb v
  have htrans (i : Fin 27) (h : InternalZero ((residuals p i).subst (newFill p)) v) :
      InternalZero ((residuals p i).subst oldFill) (extend b v) := by
    exact (equivalent_zero_iff (subst_equiv_hetero (residuals p i) oldFill (newFill p) (extend b v) v hin)).mpr h
  rw [← old_literal]
  apply (old_zero p oldFill (extend b v)).mpr
  constructor
  · exact htrans 0 h0
  · intro i
    by_cases h11 : i.succ = 11
    · apply htrans
      have h := removed_zero p v 0
      change InternalZero ((residuals p 11).subst (newFill p)) v at h
      rw [h11]
      exact h
    by_cases h12 : i.succ = 12
    · apply htrans
      have h := removed_zero p v 1
      change InternalZero ((residuals p 12).subst (newFill p)) v at h
      rw [h12]
      exact h
    by_cases h21 : i.succ = 21
    · apply htrans
      have h := removed_zero p v 2
      change InternalZero ((residuals p 21).subst (newFill p)) v at h
      rw [h21]
      exact h
    by_cases h25 : i.succ = 25
    · apply htrans
      have h := removed_zero p v 3
      change InternalZero ((residuals p 25).subst (newFill p)) v at h
      rw [h25]
      exact h
    · obtain ⟨j,hj⟩ := tail_covers i.succ (by simp) h11 h12 h21 h25
      apply htrans
      simpa only [hj] using ht j

theorem shifted_no_zero_iff (p : Fin 4 → ℤ) (b : ℕ) (hb : p 0 = (b : ℤ)) :
    (∀ v : Fin 36 → V, ¬ InternalZero (positiveShift (AdaptiveAQ36Literal.literal p)) v) ↔
      ∀ v : Fin 40 → V, ¬ InternalZero (positiveShift (AdaptiveAQ40Literal.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 40 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveAQ40Literal.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 36 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 36 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ36Literal.literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos b new hnewpos
    have holdzero := extend_zero p b hb new hnewzero
    let shifted : Fin 40 → V := fun i => AdaptiveAQ36Maps.extend b new i - 1
    have hs : (fun i => shifted i + 1) = AdaptiveAQ36Maps.extend b new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
theorem current_no_zero_iff :
    (∀ v : Fin 36 → V, ¬ InternalZero (positiveShift (AdaptiveAQ36Literal.literal CurrentWindowCarry2011.ports)) v) ↔
      ∀ v : Fin 40 → V, ¬ InternalZero (positiveShift (AdaptiveAQ40Literal.literal CurrentWindowCarry2011.ports)) v := by
  exact shifted_no_zero_iff CurrentWindowCarry2011.ports CurrentMasks2011.beta rfl

#print axioms current_no_zero_iff
#print axioms project_zero
#print axioms removed_zero
#print axioms extend_zero
#print axioms shifted_no_zero_iff
end DiophantineConsistency.AdaptiveAQ36
