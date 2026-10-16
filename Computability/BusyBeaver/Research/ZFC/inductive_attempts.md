`InductiveAttempts.lean` closes the ordinary Infinity obligation left by
`SingletonInfinity.lean`. Given the actual equality-free CP/GIC model and a
domain witness, its bisimulation quotient satisfies the exact semantic
`ZFAxioms.inf` field and the literal `Inf_form` under every valuation.
The module does not assume an earlier Infinity axiom, internal omega,
Foundation, or object-level Choice.

The argument follows the finite-attempt construction in Jeff's attributed
verification, pinned at
`297ab8df7e5de329605c3875b4934643b371a5e3`:
`ZF/stdzf/coq/Std_setrec.v:41–50,72–74,181–298` and
`Std_setinf.v:83–120`. The construction uses the least singleton index
already proved in `SingletonInfinity`; its elements need not be externally
standard natural numbers.

Fix a seed a and a definable operation G. An attempt is a set of ordered
pairs whose value at the empty index, if present, equals a. Whenever the
attempt has a value v at the singleton of z∈N, it also has a value w at z
with v=G(w). Attempts need not be total or functional in their definition.
Their backwards condition is enough for represented-set induction to prove
agreement between any two attempts at each index. A second represented-set
induction, using a one-point graph and adjunction of one graph point, proves
that every index lies in some attempt's domain. These two inductions use
the literal `agreeForm` and `hasAttemptForm` Separation instances.

The relation `Value(z,v)` says that z∈N and some attempt maps z to v.
Agreement makes this relation partial-functional on the entire domain;
the explicit z∈N guard prevents unconstrained inputs outside N. A single
literal `valueForm` Replacement instance collects its image. That image
contains a and is closed under G. There is no invocation of an internal
recursion theorem whose hypotheses already contain Infinity.

`FiniteSets.lean` supplies the fixed graph implementation using Kuratowski
pairs, singleton graphs, and finite graph adjunction. Its base extends the
no-Infinity `SingletonInfinity.Base` only by Union. Its `appForm` and
`succForm` satisfaction theorems instantiate the parametric atoms in the
attempt formulas. Taking a to be the actual empty set and G(x)=x∪{x}
therefore gives an ordinary inductive set. Including the earlier least-index
cut, the route uses three fixed Separation matrices, with their parameters,
and one fixed Replacement matrix. No Powerset operation is needed by this
generic finite-attempt step.

The final adapters use the actual quotient's checked formula-indexed
Separation and Replacement, finite constructors, and empty-root singleton
container. `quotient_infinity` returns exactly the repository's semantic
Infinity shape; `quotient_inf_form` applies the checked `bridge_Inf`.
Neither adapter postulates Separation or Collection for arbitrary external
predicates. The module establishes this axiom, rather than constructing a
complete quotient `ZFAxioms` bundle or proving the machine runtime bridge.

The pinned absolute Lean 4.32.0 compiler checked the source in 0.517 seconds
and all twenty theorem axiom audits plus three caller examples in 0.635
seconds. The callers check the semantic interface, the sealed actual
Infinity sentence, and composition from an actual `Code254.EncBundle` model
through `ModelsCPGIC`. Audited axioms are at most `propext`,
`Classical.choice`, and `Quot.sound`; two audited lemmas use no axioms.
There are no admissions, custom axioms, or `native_decide` calls.

This was a scoped check using the source-verified parent cache at
`/tmp/zfc-singleton-break-integration-0y_lh19q`; no full closure or machine
bootstrap was rebuilt. Development logs retain one unsuccessful overlay
setup and source errors involving explicit section-variable inclusion,
definitional environment reduction, and documentation placement. The final
source and audit have no warnings. Complete commands, output, hashes and
caller source are in `results/inductive-attempts-verification.json` and
`/tmp/zfc-inductive-attempts-bwz5n4pu`.
