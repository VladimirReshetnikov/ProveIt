# Generic coded cumulative clock

`PA194CumulativeClock.clock run cost` is an explicit primitive-recursive
`Code 2`, parameterized by any two finite codes: `run : Code 2` interprets a
modeled state at `(iteration, seed)`, and `cost : Code 1` interprets the
physical segment cost at a state. The clock is primitive recursion with zero
base; its step adds `cost(run(iteration, seed))` to the accumulated value.

`clockZero` and `clockSucc` prove these defining equations in **every** model
of candidate PRA, including for nonstandard iteration counts and seeds. They
make no assumption that `run` is a scheduler or `cost` is a valid physical
clock. In particular a concrete all-site source-step/cost correctness theorem,
a halt correspondence and definability of the complete induction invariant
remain separate obligations. This code alone does not prove either direction
of a machine/consistency equivalence or a new object-theory iPRA implication.
Both Lean axiom audits contain `propext`, `Classical.choice`, and `Quot.sound`,
without `sorryAx`.

## Staged source replay

`check-cumulative-clock.sh` pins and rebuilds the cumulative-clock module and
the conditional IΣ₁ model-length induction lemma in a fresh output. It checks
the coherent machine manifest and direct stepper objects, but does not rebuild
or authenticate their transitive closure. The preceding startup/header machine
baseline and project/foundation/Lake objects remain explicit prebuilt
prerequisites of the coherent build. The paths below are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-cumulative-clock.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git internal overrides and does not set them.
