# Finite invariant reflection replaces periodic-orbit bookkeeping

## Concrete target

At commit `e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11`,
`NativeFieldCycles2011.offset19_excludes_510` proves that a finite permutation
cannot carry the value 510 under the specified exceptional doubling rule.
After the existing `exception_eq_511` theorem identifies the only exceptional
source value, the old proof establishes evenness along every iterate, obtains
a positive period, constructs the `(p-1)` predecessor, and rewrites the return.

The iteration is stronger than this proof needs. Let `P i` mean `S i % 2 = 0`.
The existing `successor_mod_four` immediately implies forward preservation of
`P`. Restrict the permutation to the subset satisfying `P`. Its restriction
is injective and the subset is finite, so the restriction is surjective.
Consequently an even point has an even predecessor. Apply
`successor_mod_four` to that predecessor; the allegedly 510-valued point is
divisible by four, a contradiction.

## Existing Mathlib theorem used

`Set.Finite.injOn_iff_bijOn_of_mapsTo`, in
`Mathlib/Data/Set/Finite/Basic.lean`, converts invariance plus injectivity into
the required restricted bijection. This is an application of an existing
library theorem, not a claim that finite invariant reflection is new mathematics.
The proof-engineering novelty is replacing the explicit period and iterate
argument in this source by restricted-set surjectivity.

## Checked patch

`finite-invariant.patch` changes only one proof body and replaces the dedicated
periodic-points import by `Mathlib.Data.Set.Finite.Basic`. All declaration names
and theorem statements are unchanged. `NativeFieldCycles2011.lean` contains the
entire candidate module. `NativeFieldCyclesAudit.lean` adds only two axiom-print
commands and compiled successfully under Lean 4.32.0 with the pinned Mathlib
cache. The exact measurements and axiom outputs are in
`finite-invariant-validation.json`.

The complete module shrinks from 111 to 104 physical lines, including its
imports and all comments. The standalone `FiniteInvariant.lean` demonstrates a
generic reflection theorem and was also compiled, but is not required by the
patch and is not counted as new production source in this measurement. A
downstream project rebuild was not performed.

## Scope and non-repetition

Neither existing simplification packet proposes finite invariant reflection.
Their generic scanner invariants propagate a property forward by induction;
this argument uses finiteness and injectivity to obtain a predecessor. The
current report merely cautions that the real 511 self-loop must remain allowed.
This patch preserves that boundary and leaves `offset20_excludes_510` unchanged,
including its lack of finite-type or permutation assumptions.

The finite/injective premises cannot be omitted from the generic principle.
On the infinite type of naturals, successor preserves positivity but does not
reflect it at zero. On a finite set, a noninjective map can enter an invariant
subset from outside. The proposed application retains both required hypotheses.
