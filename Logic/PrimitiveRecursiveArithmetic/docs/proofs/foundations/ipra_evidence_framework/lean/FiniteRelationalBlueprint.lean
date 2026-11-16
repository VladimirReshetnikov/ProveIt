/-!
Evidence-indexed finite chains: Lean 4 blueprint.
STATUS: definitions and executable finite checker; not compiled in this packet.
The general correctness/embedding lemmas below are precise targets, not proofs.
No sorry, axioms, or opaque proof declarations are included.
-/
namespace FiniteRelational

/-- A finite constraint instance; predicates are Boolean and hence decidable. -/
structure Instance where
  width : Nat → Nat
  good : Nat → Nat → Bool
  edge : Nat → Nat → Nat → Bool

/-- Does a candidate at level i admit a compatible path through h? -/
def viable (P : Instance) (h : Nat) : Nat → Nat → Bool
  | i, a =>
    if hi : i < h then
      P.good i a &&
      ((List.range (P.width (i+1))).any fun b =>
        P.edge i a b && viable P h (i+1) b)
    else if i == h then P.good i a else false
termination_by h + 1 - i
-- NOTE: Lean's termination checker may require an explicit decreasing_by
-- arithmetic proof for the branch i < h. A fuel-based form avoids this.

/-- Fuel-based evaluator suitable for an uncomplicated structural recursion. -/
def viableFuel (P : Instance) (h : Nat) : Nat → Nat → Nat → Bool
  | 0, i, a => (i == h) && P.good i a
  | fuel+1, i, a =>
      if i == h then P.good i a
      else P.good i a &&
        ((List.range (P.width (i+1))).any fun b =>
          P.edge i a b && viableFuel P h fuel (i+1) b)

def hasChain (P : Instance) (h : Nat) : Bool :=
  (List.range (P.width 0)).any (viableFuel P h h 0)

/-- A finite chain is given explicitly, without a global choice operator. -/
def checkChain (P : Instance) (xs : List Nat) : Bool :=
  (List.range xs.length).all fun i =>
    match xs[i]? with
    | none => false
    | some a =>
        (a < P.width i) && P.good i a &&
          (if i+1 < xs.length then
            match xs[i+1]? with
            | some b => P.edge i a b
            | none => false
          else true)

/- Target T1: prove viableFuel P h (h-i) i a = true iff there is
   a length-(h-i+1) list starting with a and passing checkChain at levels i..h.
   Explicitly track the offset in the chain checker to avoid a false
   theorem relating a suffix to a level-zero checker.
   Proof: induction on fuel with a bound i+fuel=h, using List.any_eq_true.

   Target T2: implement bounded firstTrue : (Nat → Bool) → Nat → Option Nat,
   prove firstTrue_sound and firstTrue_complete, and recursively extract
   a chain from viableFuel=true. Verify extracted chain with checkChain.

   Target T3: represent each of width, good, edge as a fixed primitive-
   recursive numerical code, prove the Booleanization and extraction
   equations in the *object* iPRA, using only quantifier-free induction.

   Target T4: against the ProveIt project import
     ConciseIPRA.NativeBiInterpretation
   and construct, for the object formula phi, a value of actual type
     Prf PRAAx [] phi
   before applying pra_iff_native. This file intentionally does not
   construct that proof and does not claim to do so.
-/

end FiniteRelational
