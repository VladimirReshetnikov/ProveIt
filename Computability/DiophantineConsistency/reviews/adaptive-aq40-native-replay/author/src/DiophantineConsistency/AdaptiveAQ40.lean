import DiophantineConsistency.AdaptiveAQ40Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ40
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveAQ40Context AdaptiveAQ40Maps AdaptiveAQ40Zeros AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_inputs (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hz : InternalZero (AdaptiveNamedValues42.literal p) v) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  obtain ⟨ha,hq⟩ := old_relations p v hz
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · have h33 : project v 33 = v 34 := by simpa [newRest, oldRest] using project_rest v ⟨33, by decide⟩
      have h7 : project v 7 = v 7 := by simpa [newRest, oldRest] using project_rest v ⟨7, by decide⟩
      change v 18 + ((0 : V) + 0) = 0 + (project v 33 + project v 7)
      simpa only [h33,h7,zero_add,add_zero] using ha
    · simp [oldFill,newFill,splitEval,HSub.hSub,Sub.sub,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project]
      simpa only [add_comm] using hq.symm
  | inr i =>
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project_rest]

theorem extend_inputs (v : Fin 40 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · have h18 : extend v 18 = v 33 + v 7 := rfl
      change extend v 18 + ((0 : V) + 0) = 0 + (v 33 + v 7)
      simp only [h18,zero_add,add_zero]
    · simp [oldFill,newFill,splitEval,HSub.hSub,Sub.sub,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend]
      exact add_comm _ _
  | inr i =>
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend_rest]

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hz : InternalZero (AdaptiveNamedValues42.literal p) v) :
    InternalZero (AdaptiveAQ40Literal.literal p) (project v) := by
  have ho : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have hall := old_all p oldFill v ho
  have hin := project_inputs p v hz
  rw [← AdaptiveAQ40Literal.new_literal]
  apply (new_zero p newFill (project v)).mpr
  constructor
  · have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p 0) oldFill newFill v (project v) hin)
    exact eqv.mp (hall 0)
  · intro i
    have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p (tailIndex i)) oldFill newFill v (project v) hin)
    exact eqv.mp (hall (tailIndex i))

theorem extend_a_zero (p : Fin 4 → ℤ) (v : Fin 40 → V) :
    InternalZero ((residuals p 9).subst oldFill) (extend v) := by
  change InternalZero (Expr.sub (.var 18) (Expr.add (.var 34) (.var 7)) : Expr (Fin 42)) (extend v)
  have h18 : extend v 18 = v 33 + v 7 := rfl
  have h34 : extend v 34 = v 33 := rfl
  have h7 : extend v 7 = v 7 := rfl
  change extend v 18 + ((0 : V) + 0) = 0 + (extend v 34 + extend v 7)
  simp only [h18,h34,h7,zero_add,add_zero]

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 40 → V)
    (hz : InternalZero (AdaptiveAQ40Literal.literal p) v) :
    InternalZero (AdaptiveNamedValues42.literal p) (extend v) := by
  have hn : InternalZero ((newSum p).subst newFill) v := by rw [AdaptiveAQ40Literal.new_literal]; exact hz
  obtain ⟨h0,ht⟩ := (new_zero p newFill v).mp hn
  have hin := extend_inputs v
  rw [← old_literal]
  apply (old_zero p oldFill (extend v)).mpr
  constructor
  · have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p 0) oldFill newFill (extend v) v hin)
    exact eqv.mpr h0
  · intro i
    by_cases hi : i.succ = 9
    · simpa only [hi] using extend_a_zero p v
    · obtain ⟨j,hj⟩ := tail_covers i.succ (by simp) hi
      have eqv := equivalent_zero_iff (subst_equiv_hetero (residuals p (tailIndex j)) oldFill newFill (extend v) v hin)
      rw [hj] at eqv
      change InternalZero ((residuals p i.succ).subst oldFill) (extend v) ↔
        InternalZero ((residuals p i.succ).subst newFill) v at eqv
      exact eqv.mpr (by simpa only [hj] using ht j)
theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 40 → V, ¬ InternalZero (positiveShift (AdaptiveAQ40Literal.literal p)) v) ↔
      ∀ v : Fin 42 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues42.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 42 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveNamedValues42.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := project_zero p old holdzero
    let shifted : Fin 40 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 40 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (AdaptiveAQ40Literal.literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := extend_zero p new hnewzero
    let shifted : Fin 42 → V := fun i => extend new i - 1
    have hs : (fun i => shifted i + 1) = extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
#print axioms shifted_no_zero_iff
#print axioms project_zero
#print axioms extend_zero
end DiophantineConsistency.AdaptiveAQ40
