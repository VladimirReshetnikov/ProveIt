# Primitive-recursive active-prefix flag

`PA194ActivePrefix.active run hit` is an explicit `Code 2` parameterized by
finite `run : Code 2` and `hit : Code 1`. It starts at 1 and, at iteration n,
retains its previous flag if `hit(run(n,seed))` is zero, or sets it to zero
when the hit code is nonzero. The code uses candidate-PRA primitive recursion
and `selectCode`; the hit code is not assumed to be Boolean.

Theorems `activeZero`, `activeSucc` and `activeContinues` prove those exact
semantics in every candidate-PRA model. In particular, a flag of 1 at n+1
implies a flag of 1 at n and a zero hit-test at n, for arbitrary, including
nonstandard, model n. The printed Lean axioms are `propext`, `Classical.choice`
and `Quot.sound`, with no `sorryAx`.

This provides an instantiation of the prefix-step hypothesis in the separately
checked gated IΣ₁ simulation framework once `run` and `hit` are connected to
actual source behavior. It does **not** yet establish bounded first-hit
extraction, identify `hit` with a particular PA194 source halt instruction,
prove an all-site literal/source simulation or either PA consistency
implication. These are Lean all-model theorems, not newly proved iPRA formulas.

## Staged source replay

`check-active-prefix.sh` pins and rebuilds the cumulative-clock and active-
prefix sources in one fresh output, with axiom audits. The previously built
coherent machine root and general project/foundation/Lake objects are
precompiled prerequisites; the checker verifies the coherent manifest and two
direct stepper objects but does not rebuild or authenticate their full
transitive closure. Its input paths are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-active-prefix.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git internal overrides and does not set them.
