# Checked Lean semantic core

This standalone package was built successfully with **Lean 4.19.0**, using only
Lean's bundled `Std` library. It contains 31 named theorems, six proof-bearing
definitions included in the axiom audit, and 12 executable examples. There are
no `sorry` placeholders, added axiom declarations, `Classical.choice`
dependencies, or `sorryAx` dependencies in the audited declarations.

This is a checked **semantic companion** to the mathematical report. It is not
a claim that the report's major complexity theorems have already been compiled
to derivations in the object theory iPRA. See `OBJECT_IPRA_ROADMAP.md` for the
specific remaining work and the exact ProveIt interfaces inspected.

## Build

With the pinned toolchain installed through elan:

```sh
cd lean
./check.sh
```

`check.sh` runs the package build, prints axiom dependencies, and compiles the
finite examples. The captured successful output is in
`../verification/lean-build-and-axioms.log`. The source package has no network
dependencies after Lean 4.19.0 itself is installed.

## What is checked

| Module | Definitions | Checked conclusions |
| --- | --- | --- |
| `Bounded.lean` | `bany`, `ball`, `firstWitness` | Exact bounded existential/universal semantics; negative search semantics; soundness and completeness of witness extraction |
| `Machine.lean` | `iterate`, `Machine`, `acceptWithin`, `TraceOK` | Iteration addition; fixed points; acceptance monotonicity under an increased clock; uniqueness of a checked trace |
| `Reductions.lean` | Nonnegative polynomial syntax; reduction and size/cost records | Polynomial substitution/evaluation and monotonicity; explicit composition of reductions, output-size bounds, and sequential call-cost bounds |
| `Reachability.lean` | Independent relational `Walk`; finite Boolean midpoint recurrence `reach` | Walk splitting/concatenation; stutter erasure; exact equivalence with a directed walk of length at most `2^k`, with valid endpoints |
| `Circuits.lean` | Literals, clauses, CNF, gates, gate systems | Tseitin AND/NOT/constant gadget correctness; correctness of the whole concatenated gate-system constraint set; width and linear clause-count bounds |

`AxiomAudit.lean` audits all 31 theorems and the six proof-bearing definitions.
Some proofs depend on the standard Lean axioms `propext` and `Quot.sound` through
the simplifier or arithmetic tactic. Others are axiom-free. This output is
reported explicitly because an ambient Lean axiom audit and an object-iPRA
derivation are different forms of evidence. No excluded-middle or choice axiom
appears in the dependency lists.

## Exact boundaries

* `Machine` is an abstract fixed transition system, not a completed encoded
  multitape Turing-machine interpreter. `trace_unique` treats a finite prefix
  of an ambient function as a trace interface. In iPRA it becomes a packed
  finite sequence with an explicit code bound.
* `PolyCost.ticks` is a supplied operational cost. A record of this type does
  not prove that an arbitrary Lean function executes in that time. The machine
  implementation must be connected to this cost by a separate proof.
  Composition counts its two calls; a machine compiler must additionally
  account for copying and control overhead.
* `reach_iff_short_walk` is a verified correctness theorem for finite graph
  reachability. It does not yet establish configuration-count bounds,
  simple-path shortening, or a machine implementation with Savitch's space
  bound.
* `GateSystem.clauses_correct` is exact local/global constraint correctness. It
  does not include the verifier-to-circuit compiler or the proof that acyclic
  gate evaluation extends every input assignment. Thus it is a component of
  Cook--Levin, not the whole NP-completeness theorem.
* Function and predicate parameters in these modules are ambient Lean
  interfaces. They are not first-order iPRA quantifiers over arbitrary
  functions, sets, or languages. When lowering a theorem, fix its PR function
  definitions or replace a machine parameter with a finite machine code and
  retain an explicit simulation clock.
* No total primitive-recursive universal evaluator is defined or assumed.

The package deliberately keeps these boundaries visible so each subsequent
formalization step can discharge a specific obligation instead of silently
strengthening the object theory.
