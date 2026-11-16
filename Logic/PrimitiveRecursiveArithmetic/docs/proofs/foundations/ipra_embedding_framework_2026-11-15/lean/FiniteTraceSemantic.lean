import Mathlib

/-!
# Ambient semantic prototype for the finite-trace part of the framework

This file deliberately proves only ordinary Lean theorems.  It does not claim
an embedded `Prf PRAAx` derivation.  `IPRAObjectLanguageBlueprint.lean` and the
paper explain how the same recurrence is represented by fixed `PR` symbols and
proved with `PRA.qfInd`.
-/

set_option autoImplicit false

namespace CFP

structure TraceSystem (State : Type) where
  init : Nat -> State
  step : Nat -> Nat -> State -> State
  bound : Nat -> Nat
  good : Nat -> Prop
  inv : Nat -> Nat -> State -> Prop
  accept : Nat -> State -> Prop
  base : forall u, good u -> inv u 0 (init u)
  next : forall u i s, good u -> inv u i s -> inv u (i + 1) (step u i s)
  final : forall u s, good u -> inv u (bound u) s -> accept u s

namespace TraceSystem

variable {State : Type}

/-- Primitive recursion defining the state after `i` steps. -/
def run (T : TraceSystem State) (u : Nat) : Nat -> State
  | 0 => T.init u
  | i + 1 => T.step u i (run T u i)

/-- The local invariant propagates along the whole finite trace. -/
theorem run_inv (T : TraceSystem State) (u : Nat) (hu : T.good u) :
    forall i, T.inv u i (T.run u i) := by
  intro i
  induction i with
  | zero => simpa [run] using T.base u hu
  | succ i ih =>
      simpa [run, Nat.succ_eq_add_one] using T.next u i (T.run u i) hu ih

/-- The accepted conclusion follows at the primitive-recursive bound. -/
theorem sound (T : TraceSystem State) (u : Nat) (hu : T.good u) :
    T.accept u (T.run u (T.bound u)) :=
  T.final u (T.run u (T.bound u)) hu (T.run_inv u hu (T.bound u))

end TraceSystem

/-- Maximum height of a finite list, with zero for the empty list. -/
def heightMax {alpha : Type} (height : alpha -> Nat) : List alpha -> Nat
  | [] => 0
  | x :: xs => max (height x) (heightMax height xs)

/-- Every member has height at most the maximum recorded height. -/
theorem height_le_heightMax_of_mem {alpha : Type} (height : alpha -> Nat)
    {x : alpha} {xs : List alpha} (hx : x ∈ xs) :
    height x <= heightMax height xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [heightMax]
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

structure CompleteList (Param Obj : Type) (P : Param -> Obj -> Prop) where
  list : Param -> List Obj
  sound : forall a x, x ∈ list a -> P a x
  complete : forall a x, P a x -> x ∈ list a

/-- A complete finite list immediately supplies a height bound. -/
theorem CompleteList.heightBound {Param Obj : Type} {P : Param -> Obj -> Prop}
    (C : CompleteList Param Obj P) (height : Obj -> Nat) (a : Param) (x : Obj)
    (hx : P a x) :
    height x <= heightMax height (C.list a) :=
  height_le_heightMax_of_mem height (C.complete a x hx)

/-- An overlapping decision: either `x < q+d` or `q < x`.

The assumptions are phrased over an ordered additive group.  In the arithmetic
implementation all quantities are rational codes and the proof is obtained by
one decidable rational comparison after clearing denominators.
-/
theorem overlapping_branch
    {alpha : Type} [LinearOrderedField alpha]
    (x a q e d : alpha) (he : 0 <= e) (hd : 4 * e <= d)
    (happrox : |x - a| <= e) : x < q + d ∨ q < x := by
  by_cases h : a <= q + d / 2
  · left
    have hxa : x <= a + e := by
      have := (abs_le.mp happrox).2
      linarith
    have hed : e <= d / 4 := by linarith
    linarith
  · right
    have haq : q + d / 2 < a := lt_of_not_ge h
    have hax : a - e <= x := by
      have := (abs_le.mp happrox).1
      linarith
    have hed : e <= d / 4 := by linarith
    linarith

end CFP
