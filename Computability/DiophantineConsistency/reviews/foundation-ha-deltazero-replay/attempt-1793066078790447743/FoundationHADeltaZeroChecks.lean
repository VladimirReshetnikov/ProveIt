import DiophantineConsistency.FoundationHADeltaZero

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHADeltaZeroChecks
open LO LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax HABoundedQuantifiers FoundationHADeltaZero
open scoped LO.FirstOrder

-- A zero bound is syntactically Positive, whereas the bound witness is not.
example : (.func .zero Fin.elim0 : Semiterm ℒₒᵣ Nat 1).Positive := by simp
example : ¬((.bvar 0 : Semiterm ℒₒᵣ Nat 1).Positive) := by simp

-- The fresh bound witness and an old bound slot remain distinct.
example (bv : Fin 2 → PTerm) (fv : Nat → PTerm) :
    ordinaryAux bv fv (.all (.rel .eq ![.bvar 0, .bvar 2])) =
      .all (.eq (.var 0) (SetTheory.PA.Term.rename Nat.succ (bv 1))) := rfl

-- Two nested binders shift ambient free parameters twice, not the witnesses.
example (bv : Fin 1 → PTerm) (fv : Nat → PTerm) :
    ordinaryAux bv fv (.all (.exs (.nrel .lt ![.bvar 1, .fvar 7]))) =
      .all (.ex (neg (ltFormula (.var 1)
        (SetTheory.PA.Term.rename Nat.succ (SetTheory.PA.Term.rename Nat.succ (fv 7)))))) := rfl

-- The bound itself may be zero or contain sparse ambient free parameters.
example (bv : Fin 0 → PTerm) (fv : Nat → PTerm)
    (p : Semiformula ℒₒᵣ Nat 1) :
    ordinaryAux bv fv (∃⁰[“x. x < !!(Rew.bShift (.func .zero Fin.elim0 : Semiterm ℒₒᵣ Nat 0))”] p) =
      bex .zero (ordinaryAux (liftBound bv) (liftFree fv) p) := ordinary_bex bv fv (.func .zero Fin.elim0) p

private def sample : Semiformula ℒₒᵣ Nat 0 :=
  ∀⁰[“x. x < !!(Rew.bShift (&7 : Semiterm ℒₒᵣ Nat 0))”]
    (∃⁰[“y. y < !!(Rew.bShift (#0 : Semiterm ℒₒᵣ Nat 1))”]
      ((Semiformula.rel .eq ![#0, #1]) ⋎ (Semiformula.nrel .lt ![#1, &9])))

private theorem sample_bounded : LO.FirstOrder.Arithmetic.DeltaZero sample := by
  apply LO.FirstOrder.Arithmetic.Hierarchy.ball (Rew.bShift_positive _)
  apply LO.FirstOrder.Arithmetic.Hierarchy.bexs (Rew.bShift_positive _)
  exact .or (.rel _ _ _ _) (.nrel _ _ _ _)

example (fv : Nat → PTerm) : Proves (dec (ordinaryAux Fin.elim0 fv sample)) :=
  ordinary_decidable sample_bounded Fin.elim0 fv

example : Proves (dec (ordinaryAux Fin.elim0
    (fun i => .add (.var (3*i+2)) (.succ (.var 0))) sample)) :=
  ordinary_decidable sample_bounded _ _

example (fv : Nat → PTerm) (G : List SetTheory.PA.Formula) :
    Relative SetTheory.PA.Formula.Ax_s (G.map (SetTheory.PA.Formula.rename Nat.succ))
      (dec (ordinaryAux Fin.elim0 (liftFree fv) sample)) :=
  ordinary_decidable_relative sample_bounded _ _ _

example (t : PTerm) (a : SetTheory.PA.Formula) (h : Proves (dec a)) :
    Proves (dec (.all (.or (neg (ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ t))) a))) :=
  guarded_all_decidable t a h

#print axioms ordinaryAux
#print axioms positive_bound
#print axioms ordinary_ball
#print axioms ordinary_bex
#print axioms guard_forward
#print axioms guard_reverse
#print axioms all_imp
#print axioms guarded_all_decidable
#print axioms hierarchy_zero_decidable
#print axioms ordinary_decidable
#print axioms ordinary_decidable_relative
#print axioms sample_bounded
end DiophantineConsistency.FoundationHADeltaZeroChecks
