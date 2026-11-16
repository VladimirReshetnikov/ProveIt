# Lean formalization plan

Baseline: `VladimirReshetnikov/ProveIt` commit
`f444b76e8480ebea128c15b4a59f158e14f478cc` (2026-11-16).

## Status

`ScopedCertificate/Kernel.lean` is a source-level, no-placeholder candidate
using only constructors and checked structural theorems of `Prf PRAAx`.  It was
not elaborated here because Lean was absent from the artifact runtime.  The
larger file is a blueprint and intentionally declares no unproved object
results.

## Proposed integration

Place the implementation under
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Framework/ScopedCertificate/`
and expose it through `IPRADerivations.lean`.  Keep the Foundation bridge
extension in `Logic/PrimitiveRecursiveArithmetic/Bridge/Lean/IPRABridge/Open.lean`.

## Milestones

1. **Structural kernel.** Elaborate `Kernel.lean`; add checks for `boundary`,
   `discharge`, `replaceContext`, `specialize`, `Contract.close`, and
   `Contract.conditional`.  Add all declarations to the axiom audit.
2. **Reflected bits.** Define a small host syntax of *fixed* bounded formulas.
   Each atom carries a characteristic `PTm` and two object derivations.  Compile
   conjunction, disjunction, implication, bounded existential and bounded
   universal using existing `eqb`, order, bounded sums/products and search.
3. **Selection adapter.** Wrap `Search.mu`, `search_found`, and
   `search_minimal` as the theorem `leastAccepted`; prove the sentinel case.
4. **Trace core.** Add fixed-base digit extraction using `Core.Division`; define
   action decoding, state recursion, failure accumulation and the prefix
   invariant.  The central induction formula must remain quantifier-free.
5. **Strategies.** For each fixed alternation shape, compile a strategy table
   and its verifier.  Begin with `forall-exists` and `exists-forall`, then add a
   meta-level recursion over fixed shapes.
6. **Observers.** Prove exact certificate independence, diameter composition,
   quotient-respecting substitution and the separation/gap lemma.
7. **Open bridge.** Publicly wrap the existing open Concise-to-Foundation
   theorem.  For the reverse direction, translate a finite-context Hilbert
   proof after repeated deduction, translate the implication chain under an
   arbitrary free-term environment, and reopen it by modus ponens.  Prove the
   Foundation-code round trip by induction on PR codes, using qf induction in
   the primitive-recursion case.
8. **Pilots.** Migrate one finite arithmetic packet, the exact cubic bisection
   example, one finite carrier/topology example, and one conditional
   height-bounded Diophantine list.

## Acceptance gates

- `lake build IPRADerivations`
- focused builds of every new module
- `#print axioms` entries matching the repository policy and no `sorryAx`
- substitution tests at non-variable terms
- an induction test with a parameter under a binder
- a trace with a changing resource parameter
- a path example where the least local move is a dead end
- an observer example with two different valid certificates
- a boundary theorem whose missing producer is visible in the final type
- both directions of an open-sequent bridge test
