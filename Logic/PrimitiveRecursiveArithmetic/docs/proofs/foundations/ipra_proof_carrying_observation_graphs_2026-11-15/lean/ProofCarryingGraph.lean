/-!
# Proof-carrying observation graphs: proposed ConciseIPRA integration module

This file is a source-oriented formalization outline tied to the actual
repository API.  It is intended to live in the `ConciseIPRA` Lake library after
moving the already checked `LocalGlobal.ObjectIteration` declarations into a
library module `ConciseIPRA.FiniteTrace`.

The declarations below contain no semantic truth-to-provability rule.  Every
edge of a graph is a host-level function that consumes actual embedded
`Prf PRAAx` derivations and returns another such derivation.

The preparation environment for this archive did not contain Lean, so this
file has not been elaborated here.  The core definitions are deliberately
small and the implementation plan names every import and expected repair.
-/

import ConciseIPRA.PR
-- Proposed upstream module, obtained by integrating the already checked file
-- docs/proofs/foundations/ipra_local_global/lean/ObjectIteration.lean:
import ConciseIPRA.FiniteTrace

namespace LeanProofs.ConciseIPRA.PCOG

open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.LocalGlobal

/-- A bounded primitive-recursive trace together with the two *object-theory*
proofs needed by `primitiveRecursionInvariant`. -/
structure TracePackage (k : Nat) (Γ : List (Fm PTm k)) where
  init       : PR k
  step       : PR (k + 2)
  invariant  : Fm PTm (k + 2)
  invariantQF : invariant.QF
  base       : Γ ⊢[PRAAx] baseFormula init invariant
  advance    : invariant :: (Γ.map Fm.shift).map Fm.shift
                 ⊢[PRAAx] nextFormula step invariant

namespace TracePackage

variable {k : Nat} {Γ : List (Fm PTm k)}

/-- The precise terminal formula delivered by the trace theorem at a supplied
primitive-recursive fuel term. -/
def terminal (T : TracePackage k Γ) (fuel : PTm k) : Fm PTm k :=
  instStateTime T.invariant (runTerm T.init T.step fuel var) fuel var

/-- This is only a wrapper around the repository's checked object-iPRA rule. -/
theorem runAt (T : TracePackage k Γ) (fuel : PTm k) :
    Γ ⊢[PRAAx] T.terminal fuel :=
  primitiveRecursionAt T.init T.step T.invariant T.invariantQF Γ
    T.base T.advance fuel

end TracePackage

/-- A finalizer discharges a terminal invariant to a theorem-specific output.
The finalizer itself is again an actual object derivation. -/
structure TraceExit {k : Nat} {Γ : List (Fm PTm k)}
    (T : TracePackage k Γ) where
  fuel   : PTm k
  output : Fm PTm k
  finish : T.terminal fuel :: Γ ⊢[PRAAx] output

namespace TraceExit

variable {k : Nat} {Γ : List (Fm PTm k)} {T : TracePackage k Γ}

/-- Compile a trace package and its finalizer to the advertised output. -/
theorem compile (E : TraceExit T) : Γ ⊢[PRAAx] E.output := by
  apply E.finish.trans
  intro A hA
  simp only [List.mem_cons] at hA
  rcases hA with hA | hA
  · subst A
    exact T.runAt E.fuel
  · exact Prf.hyp hA

end TraceExit

/-- A proof-producing graph node.  `derive` is a meta-level proof constructor,
not a coded universal evaluator and not a reflection principle. -/
structure Rule (n : Nat) where
  inputs : List (Fm PTm n)
  output : Fm PTm n
  derive : ∀ Γ : List (Fm PTm n),
    (∀ A, A ∈ inputs → Γ ⊢[PRAAx] A) → Γ ⊢[PRAAx] output

/-- A topologically compiled prefix of a graph. -/
structure Compiled (n : Nat) (Γ : List (Fm PTm n)) where
  outputs : List (Fm PTm n)
  derives : ∀ {A}, A ∈ outputs → Γ ⊢[PRAAx] A

namespace Compiled

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- Empty compiled graph. -/
def empty : Compiled n Γ where
  outputs := []
  derives := by
    intro A h
    cases h

/-- Add one node whose requirements occur in the compiled prefix.  This is the
host-level cut step used by the staged internalization theorem. -/
def extend (C : Compiled n Γ) (R : Rule n)
    (deps : R.inputs ⊆ C.outputs) : Compiled n Γ where
  outputs := R.output :: C.outputs
  derives := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A
      exact R.derive Γ (fun B hB => C.derives (deps hB))
    · exact C.derives hA

/-- Read the newest graph output. -/
theorem head (C : Compiled n Γ) {A : Fm PTm n}
    (h : A ∈ C.outputs) : Γ ⊢[PRAAx] A :=
  C.derives h

end Compiled

/-- Turn a completed bounded trace into a graph rule with no additional input
formula beyond the ambient context used by the trace package. -/
def Rule.ofTraceExit {k : Nat} {Γ : List (Fm PTm k)}
    {T : TracePackage k Γ} (E : TraceExit T) : Rule k where
  inputs := Γ
  output := E.output
  derive := by
    intro Δ hΓ
    exact (E.compile).trans (fun A hA => hΓ A hA)

/-- Local certificate comparison, matching the checked combinator in
`ObjectObservation.lean`.  Kept here to make the graph interface explicit. -/
def Rule.ofBinaryStability {n : Nat}
    (C₁ C₂ O : Fm PTm n)
    (stable : C₁ :: C₂ :: ([] : List (Fm PTm n)) ⊢[PRAAx] O) : Rule n where
  inputs := [C₁, C₂]
  output := O
  derive := by
    intro Γ h
    have h₁ : Γ ⊢[PRAAx] C₁ := h C₁ (by simp)
    have h₂ : Γ ⊢[PRAAx] C₂ := h C₂ (by simp)
    have hs : C₁ :: C₂ :: Γ ⊢[PRAAx] O :=
      stable.weaken (by
        intro A hA
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl <;> simp)
    exact Prf.impE (Prf.impE (Prf.impI (Prf.impI hs)) h₂) h₁

/-!
The remaining compiler is intentionally *staged*.

A host function traverses a fixed `Array NodeSpec` in topological order and
constructs `Rule` values.  Recursive nodes are first converted to
`TracePackage` values; relational nodes use bounded-search/viability packages;
exact nodes use defining-equation derivations.  Repeated `Compiled.extend`
then returns the final `Prf PRAAx` proof.

No theorem in this module quantifies over a numeric code of an arbitrary PR
program.  Consequently the construction does not conflict with the diagonal
obstruction to a total primitive-recursive universal evaluator.
-/

end LeanProofs.ConciseIPRA.PCOG
