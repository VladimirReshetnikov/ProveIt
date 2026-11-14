# Generic positive-simulation halting theorem

`PA195GenericTrace.lean` proves a standard-natural-number halting equivalence
for deterministic partial transition functions. It assumes a parent invariant
that is preserved by transitions, a projection to child configurations,
positive-length child simulations of parent steps, totality of parent steps at
invariant nonhalting configurations, preservation of the halt predicate by the
projection, and absence of child transitions out of a halting configuration.

The forward direction concatenates simulations. The reverse direction assumes
the parent never halts and extends it for one more step than the child halt
time; positive simulation gives a longer child run, contradicting the halted
child having no next step. The theorem does not itself instantiate these
assumptions for the PA195 machine or prove anything inside PRA or iPRA.

Check from the repository root:

```sh
lake env lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa195-generic-trace/PA195GenericTrace.lean
```

The reported theorem axioms are `propext`, `Classical.choice`, and
`Quot.sound`.
