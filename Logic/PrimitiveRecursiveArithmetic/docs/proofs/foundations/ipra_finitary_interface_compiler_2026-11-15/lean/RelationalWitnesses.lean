import ConciseIPRA.PR

/-!
# Finite relational witnesses, backward viability, and stable erasure

This file contains both an executable finite semantic model and the exact
object-language target data.  It was not compiled in the artifact environment.
Visible `sorry` terms mark the remaining proof work.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryInterface

/-! ## Executable finite semantic model -/

structure FiniteTower where
  level : Nat → List Nat
  valid : Nat → Nat → Bool
  edge : Nat → Nat → Nat → Bool

/-- Viability for exactly `fuel` remaining edges. -/
def FiniteTower.viable (T : FiniteTower) : Nat → Nat → Nat → Bool
  | 0, p, a => T.valid p a
  | fuel + 1, p, a =>
      T.valid p a &&
        (T.level (p + 1)).any fun b =>
          T.edge p a b && T.viable fuel (p + 1) b

/-- A path beginning at level `p` is valid when all candidates are valid and
all consecutive entries satisfy the edge relation. -/
def FiniteTower.PathValid (T : FiniteTower) : Nat → List Nat → Prop
  | _, [] => False
  | p, [a] => T.valid p a = true
  | p, a :: b :: rest =>
      T.valid p a = true ∧ T.edge p a b = true ∧
        T.PathValid (p + 1) (b :: rest)

/-- Viability is exactly existence of a full finite compatible path. -/
theorem viability_iff_finite_path (T : FiniteTower) (fuel p a : Nat) :
    T.viable fuel p a = true ↔
      ∃ tail : List Nat,
        tail.length = fuel ∧ T.PathValid p (a :: tail) := by
  sorry

/-- Least viable path.  `none` is the totalized failure value. -/
def FiniteTower.leastPath (T : FiniteTower) (fuel p : Nat) : Option (List Nat) :=
  let starts := (T.level p).filter fun a => T.viable fuel p a
  match starts.head? with
  | none => none
  | some a =>
      let rec extend : Nat → Nat → Nat → Option (List Nat)
        | 0, _, current => some [current]
        | remaining + 1, level, current =>
            let nexts := (T.level (level + 1)).filter fun b =>
              T.edge level current b && T.viable remaining (level + 1) b
            match nexts.head? with
            | none => none
            | some b =>
                match extend remaining (level + 1) b with
                | none => none
                | some tail => some (current :: tail)
      extend fuel p a


theorem leastPath_sound (T : FiniteTower) {fuel p : Nat} {path : List Nat}
    (h : T.leastPath fuel p = some path) :
    path.length = fuel + 1 ∧ T.PathValid p path := by
  sorry

/-- Total terminal-value helper; valid full paths are nonempty. -/
def terminal : List Nat → Nat
  | [] => 0
  | [a] => a
  | _ :: rest => terminal rest

/-- Exact stable erasure: all valid full paths have the same observation. -/
theorem stable_erasure (T : FiniteTower) (observe : Nat → Nat)
    (fuel p : Nat)
    (hstable : ∀ α β,
      α.length = fuel + 1 → β.length = fuel + 1 →
      T.PathValid p α → T.PathValid p β →
      observe (terminal α) = observe (terminal β))
    {path : List Nat} (hpath : T.leastPath fuel p = some path)
    {other : List Nat} (hlen : other.length = fuel + 1)
    (hother : T.PathValid p other) :
    observe (terminal path) = observe (terminal other) := by
  sorry

/-! ## Object-language primitive-recursive data -/

/-- Primitive-recursive finite cloud data.  `value(i,j,x)` is candidate `j`
at level `i`; `valid` and `edge` are Boolean-valued. -/
structure RelTowerPR where
  levelBound : PR 2   -- level, input
  value      : PR 3   -- level, candidate index, input
  valid      : PR 3   -- level, candidate index, input
  edge       : PR 4   -- level, old index, new index, input

/-- A finite horizon is handled by backwards primitive recursion on the
remaining distance.  The intended arguments are horizon, level, candidate
index, and input. -/
def viableSymbol (_T : RelTowerPR) : PR 4 := by
  -- Implement the semantic recursion above with a bounded existential fold.
  sorry

/-- Least viable successor.  Totalize by returning zero when no witness exists;
the contract consumes a proof that a viable successor exists. -/
def leastViableSuccessor (_T : RelTowerPR) : PR 4 := by
  -- Arguments: remaining distance, level, current index, input.
  sorry

/-- Object-language target: Boolean viability is equivalent to a bounded path
verifier.  The real theorem will return a `Prf PRAAx` derivation of the
corresponding `Fm.iff`. -/
theorem viabilityReflectionTarget : True := by
  trivial

/-- Shrinking viability target.  A primitive-recursive diameter modulus and a
summable motion budget make selections at changing finite horizons into a
regular name; no infinite branch is selected. -/
theorem shrinkingViabilityRegularNameTarget : True := by
  trivial

end LeanProofs.ConciseIPRA.FinitaryInterface
