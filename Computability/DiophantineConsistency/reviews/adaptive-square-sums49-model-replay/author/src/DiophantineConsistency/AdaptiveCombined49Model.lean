import DiophantineConsistency.AdaptiveCombined49Context
import DiophantineConsistency.AdaptiveCombined49Strong
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveCombined49Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveCombined49Context AdaptiveCombined49Strong
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def collapse (v : Fin 50 → V) (i : Fin 49) : V :=
  if h : i.val < 40 then v ⟨i.val, by omega⟩
  else if i.val = 40 then v 38 * v 38 else v ⟨i.val + 1, by omega⟩

def expand (v : Fin 49 → V) (i : Fin 50) : V :=
  if h : i.val < 40 then v ⟨i.val, by omega⟩
  else if i.val = 40 then v 40 + 1
  else if i.val = 41 then 1 else v ⟨i.val - 1, by omega⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem collapse_rest (v : Fin 50 → V) (i : Fin 48) :
    collapse v (newRest i) = v (oldRest i) := by
  by_cases h : i.val < 40
  · simp [collapse,newRest,oldRest,h]
  · have h1 : ¬ i.val + 1 < 40 := by omega
    have h2 : i.val ≠ 39 := by omega
    simp [collapse,newRest,oldRest,h,h1,h2,Nat.add_assoc]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem expand_rest (v : Fin 49 → V) (i : Fin 48) :
    expand v (oldRest i) = v (newRest i) := by
  by_cases h : i.val < 40
  · simp [expand,newRest,oldRest,h]
  · have h1 : ¬ i.val + 2 < 40 := by omega
    have h2 : i.val ≠ 38 := by omega
    have h3 : i.val ≠ 39 := by omega
    simp [expand,newRest,oldRest,h,h1,h2,h3]

theorem collapse_pos (v : Fin 50 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < collapse v i := by
  intro i
  unfold collapse
  split
  · exact hv _
  · split
    · exact mul_pos (hv 38) (hv 38)
    · exact hv _

theorem expand_pos (v : Fin 49 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < expand v i := by
  intro i
  unfold expand
  split
  · exact hv _
  · split
    · exact add_pos (hv 40) Arithmetic.zero_lt_one
    · split
      · exact Arithmetic.zero_lt_one
      · exact hv _

private theorem subst_equiv_hetero {σ τ υ : Type*} (e : Expr σ) (f : σ → Expr τ) (g : σ → Expr υ)
    (v : τ → V) (w : υ → V)
    (h : ∀ i, Equivalent (splitEval (f i) v) (splitEval (g i) w)) :
    Equivalent (splitEval (e.subst f) v) (splitEval (e.subst g) w) := by
  induction e with
  | constant c => exact equivalent_refl _
  | var i => exact h i
  | add p q hp hq =>
      change Equivalent (splitEval (p.subst f + q.subst f) v) (splitEval (p.subst g + q.subst g) w)
      rw [splitEval_add,splitEval_add]
      exact plus_equiv hp hq
  | sub p q hp hq =>
      change Equivalent (splitEval (p.subst f - q.subst f) v) (splitEval (p.subst g - q.subst g) w)
      rw [splitEval_sub,splitEval_sub]
      exact minus_equiv hp hq
  | mul p q hp hq =>
      change Equivalent (splitEval (p.subst f * q.subst f) v) (splitEval (p.subst g * q.subst g) w)
      rw [splitEval_mul,splitEval_mul]
      exact equivalent_multiply hp hq

theorem collapse_zero (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (hz : InternalZero (AdaptiveNamedValues50.literal p) v) : InternalZero (literal p) (collapse v) := by
  have hr := strong_relation p v hz
  have hh : ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (collapse v)) := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      simp [oldFill,newFill,splitEval,HSub.hSub,Sub.sub,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,collapse]
      simpa only [add_comm] using hr.symm
    | inr i =>
      simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,collapse_rest]
  have h := subst_equiv_hetero (contextQ p) oldFill newFill v (collapse v) hh
  have eqv := equivalent_zero_iff h
  rw [old_context] at eqv
  exact eqv.mp hz

theorem expand_zero (p : Fin 4 → ℤ) (v : Fin 49 → V)
    (hz : InternalZero (literal p) v) : InternalZero (AdaptiveNamedValues50.literal p) (expand v) := by
  have hh : ∀ i, Equivalent (splitEval (oldFill i) (expand v)) (splitEval (newFill i) v) := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      simp [oldFill,newFill,splitEval,HSub.hSub,Sub.sub,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,expand]
      exact add_comm _ _
    | inr i =>
      simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,expand_rest]
  have h := subst_equiv_hetero (contextQ p) oldFill newFill (expand v) v hh
  have eqv := equivalent_zero_iff h
  rw [old_context] at eqv
  exact eqv.mpr hz
theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 49 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
      ∀ v : Fin 50 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues50.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 50 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveNamedValues50.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := collapse_pos old holdpos
    have hnewzero := collapse_zero p old holdzero
    let shifted : Fin 49 → V := fun i => collapse old i - 1
    have hs : (fun i => shifted i + 1) = collapse old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 49 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := expand_pos new hnewpos
    have holdzero := expand_zero p new hnewzero
    let shifted : Fin 50 → V := fun i => expand new i - 1
    have hs : (fun i => shifted i + 1) = expand new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
end DiophantineConsistency.AdaptiveCombined49Model
