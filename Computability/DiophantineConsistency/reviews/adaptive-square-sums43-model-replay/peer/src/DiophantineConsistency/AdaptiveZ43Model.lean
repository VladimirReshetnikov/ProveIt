import DiophantineConsistency.AdaptiveZ43Maps
import DiophantineConsistency.AdaptiveZ46Rest
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiophantineConsistency.AdaptiveZ43Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveZ43Context AdaptiveZ43Maps AdaptiveZ43PositiveActual AdaptiveZ46Rest
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 44 → V) (hb : (2:V)≤(p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveZ44Context.literal (fun j => (p j:ℤ))) v) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v)) := by
  have hd := signed_d_positive p v hb hv hz
  intro i
  cases i with
  | inl i =>
    fin_cases i
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project,HSub.hSub,Sub.sub]
    exact ((add_comm _ _).trans (tsub_add_cancel_of_le (le_of_lt hd))).symm
  | inr i =>
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project_rest]

theorem extend_inputs (v : Fin 43 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend,HSub.hSub,Sub.sub,add_comm]
  | inr i =>
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend_rest]

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 44 → V) (hb : (2:V)≤(p 0:V)) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveZ44Context.literal (fun j => (p j:ℤ))) v) :
    InternalZero (literal (fun j => (p j:ℤ))) (project v) := by
  rw [← old_literal] at hz
  rw [← new_literal]
  exact (equivalent_zero_iff (subst_equiv_hetero (sum (fun j => (p j:ℤ))) oldFill newFill v (project v) (project_inputs p v hb hv (by rw [← old_literal]; exact hz)))).mp hz

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 43 → V)
    (hz : InternalZero (literal p) v) : InternalZero (AdaptiveZ44Context.literal p) (extend v) := by
  rw [← old_literal, ← new_literal] at *
  exact (equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill (extend v) v (extend_inputs v))).mpr hz
theorem shifted_no_zero_iff (p : Fin 4 → ℕ) (hb : (2:V)≤(p 0:V)) :
    (∀ v : Fin 43 → V, ¬ InternalZero (positiveShift (literal (fun j => (p j:ℤ)))) v) ↔
      ∀ v : Fin 44 → V, ¬ InternalZero (positiveShift (AdaptiveZ44Context.literal (fun j => (p j:ℤ)))) v := by
  constructor
  · intro h v hz
    let old : Fin 44 → V := fun i => v i + 1
    have holdpos : ∀ i, 0 < old i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have holdzero : InternalZero (AdaptiveZ44Context.literal (fun j => (p j:ℤ))) old :=
      (internalZero_positiveShift _ _).mp hz
    have hnewpos := project_pos p old hb holdpos holdzero
    have hnewzero := project_zero p old hb holdpos holdzero
    let shifted : Fin 43 → V := fun i => project old i - 1
    have hs : (fun i => shifted i + 1) = project old := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact hnewzero
  · intro h v hz
    let new : Fin 43 → V := fun i => v i + 1
    have hnewpos : ∀ i, 0 < new i := by
      intro i
      exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hnewzero : InternalZero (literal (fun j => (p j:ℤ))) new :=
      (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hnewpos
    have holdzero := extend_zero (fun j => (p j:ℤ)) new hnewzero
    let shifted : Fin 44 → V := fun i => extend new i - 1
    have hs : (fun i => shifted i + 1) = extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift, hs]
    exact holdzero
#print axioms shifted_no_zero_iff
#print axioms project_zero
#print axioms extend_zero
end DiophantineConsistency.AdaptiveZ43Model
