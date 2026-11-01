import DiophantineConsistency.AdaptiveNamedValues47Zeros
import DiophantineConsistency.AdaptiveNamedValues47Maps
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues47Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveNamedValues47Context AdaptiveNamedValues47Zeros AdaptiveNamedValues47Maps
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
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

theorem collapse_zero (p : Fin 4 → ℤ) (v : Fin 49 → V)
    (hz : InternalZero (AdaptiveNamedValues49.literal p) v) : InternalZero (literal p) (project v) := by
  have ho : ∀ i : Fin 35, InternalZero ((residuals p i).subst oldFill) v :=
    (old_all p oldFill v).mp (by change InternalZero (AdaptiveNamedValues49.literal p) v; exact hz)
  have hc := ho 8
  have ha := ho 9
  change InternalZero ((.var 17) - ((.var 9) + (.var 42)) : Expr (Fin 49)) v at hc
  change InternalZero ((.var 18) - ((.var 34) + (.var 7)) : Expr (Fin 49)) v at ha
  simp [InternalZero, pairEval, splitEval, Expr.splitNatural, NatExpr.evalSemiring,
    HSub.hSub, Sub.sub] at hc ha
  have hh : ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
    intro i
    cases i with
    | inl i =>
      fin_cases i <;> simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,
        Equivalent,project,oldRest,hc,ha]
    | inr i =>
      simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project]
  change InternalZero ((newSum p).subst newFill) (project v)
  apply (new_all p newFill (project v)).mpr
  intro i hi hj
  have h := subst_equiv_hetero (residuals p i) oldFill newFill v (project v) hh
  exact (equivalent_zero_iff h).mp (ho i)

theorem expand_zero (p : Fin 4 → ℤ) (v : Fin 47 → V)
    (hz : InternalZero (literal p) v) : InternalZero (AdaptiveNamedValues49.literal p) (extend v) := by
  have hn : ∀ i : Fin 35, i ≠ 8 → i ≠ 9 → InternalZero ((residuals p i).subst newFill) v :=
    (new_all p newFill v).mp (by change InternalZero (literal p) v; exact hz)
  have hh : ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
    intro i
    cases i with
    | inl i =>
      fin_cases i <;> simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,
        Equivalent,extend]
    | inr i =>
      simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend_rest]
  change InternalZero ((oldSum p).subst oldFill) (extend v)
  apply (old_all p oldFill (extend v)).mpr
  intro i
  by_cases hi : i = 8
  · subst i
    change InternalZero ((.var 17) - ((.var 9) + (.var 42)) : Expr (Fin 49)) (extend v)
    simp [InternalZero,pairEval,splitEval,Expr.splitNatural,NatExpr.evalSemiring,
      HSub.hSub,Sub.sub]
    simp [extend]
  by_cases hj : i = 9
  · subst i
    change InternalZero ((.var 18) - ((.var 34) + (.var 7)) : Expr (Fin 49)) (extend v)
    simp [InternalZero,pairEval,splitEval,Expr.splitNatural,NatExpr.evalSemiring,
      HSub.hSub,Sub.sub]
    simp [extend]
  have h := subst_equiv_hetero (residuals p i) oldFill newFill (extend v) v hh
  exact (equivalent_zero_iff h).mpr (hn i hi hj)
theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 47 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
      ∀ v : Fin 49 → V, ¬ InternalZero (positiveShift (AdaptiveNamedValues49.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 49 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveNamedValues49.literal p) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos old holdpos
    have hnewzero := collapse_zero p old holdzero
    let shifted : Fin 47 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 47 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := expand_zero p new hnewzero
    let shifted : Fin 49 → V := fun i => extend new i - 1
    have hs : (fun i => shifted i + 1) = extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero

#print axioms shifted_no_zero_iff
end DiophantineConsistency.AdaptiveNamedValues47Model
