# Counterexample case with one universal guard

`ParsonsCounterFresh.counter_one_universal` composes the fresh-variable
cut-free inversion with the existing induction counterexample case. Its side
context has one universal formula `∀x A(x)` with a Σ₁ body and an arbitrary
remaining marked context whose projected side disjunction is Σ₁. Given the
three explicitly stated base, step, and negative recursive cases, each on an
actual cut-free derivation of height strictly below the original existential
conclusion, it constructs an actual PA-minus rule proof of the original marked
output. The proof shifts all marked entries and parameter terms, opens the
universal side, applies the existing counterexample case, and universally
closes the result.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-counter-fresh-replay/FILES.json) has SHA-256
`65cb0c3e7fedae245ac3e2c92b49bec974a2e3cc1d15f9a87881ab3cc3bdd794`.
The direct `ParsonsFreshOpen` source hash
`3dd42344fdd5a16be931ef094b5ad9d10996688c0aa9e4dcec435b6642785ae1`
matches its frozen snapshot, and its object hash is
`e89de03bf2a3fd75c382ba46aecd5d1e26c9fdab7d89429ee2f5aaad4f8b42e5`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

The three recursive premises are explicit hypotheses, not established by this
local theorem. Its Σ₁ remainder assumption is material; arbitrary non-prenex
Π₂ guards, complete case dispatch, the global recursion, conservation, and
PRA-provability of the target equivalence remain open. The existing HA result
for the 14-variable PDF equation is separate and already proved in Lean.

A third independent replay at `/tmp/parsons-counter-fresh-build-lpl0yo0d`
also passed; both source, object, and complete log hashes match the two
recorded builds. The same inherited-provider qualification applies.
