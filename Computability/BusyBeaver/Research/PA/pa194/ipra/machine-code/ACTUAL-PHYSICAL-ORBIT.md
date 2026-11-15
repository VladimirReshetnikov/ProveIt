# Model-length physical loop with exact primitive-recursive clock

`PA194ActualLoopExactStep.exactOneStep` composes the site-27,
site-28, site-29, and site-30 literal physical transitions in every PRA model.
The physical clock is a primitive-recursive code assembled from the exact
segment clocks. The tested source register must have a successor value. The
other eight source registers, controller tail, spare block value, model-valued
count of trailing one-blocks, and header gap are arbitrary within the displayed
frame; the far end after those blocks is zero.

`PA194ActualPhysicalOrbit.physicalOrbit` iterates that transition through
any model-valued number of iterations up to the initial register 0. Its
primitive-recursive cumulative clock is explicit. The output stays at site 27;
register 0 decreases by the number of iterations, registers 6 and 8 each grow
by it, the gap grows by it, and the trailing-block count grows by twice it.
Open induction in PRA suffices for the source orbit and clocked iteration; no
additional IΣ₁ model hypothesis is used. This is a model-theoretic Lean
statement. The [native iPRA sentence](ACTUAL-PHYSICAL-NATIVE.md) internalizes
the completed loop. It is one loop of the source
program, not a full model-uniform simulation and not either direction of the
PA consistency equivalence.

`check-actual-physical-orbit.sh` rebuilds the controller/physical
source closure, the conditional iteration, the exact clock modules, and the
unconditional composition in one temporary output. It uses the same 26
arguments as `check-actual-loop-orbit.sh` and audits source hashes, selected
machine overlays, overlapping machine objects, and printed theorem axioms.
The machine stages, code graph, and general foundations remain prebuilt; the
checker does not authenticate their complete transitive source closure. The replay exited 0; its log is
`/tmp/pa194-actual-physical-orbit-check.log`.

The iteration sources rebuilt in the shared temporary output are:
`PA194ModelLoopIteration`, `PA194ModelLoopState`, `PA194ModelLoopFrame`,
`PA194ModelSourceLoop`, `PA194ModelLoopFour`, `PA194ControllerLoopFrame`,
`PA194ActualSourceLoop`, `PA194ActualSourceRun`, `PA194ActualSourceExit`,
`PA194ActualSourceRunSentence`, `PA194ActualSourceExitSentence`,
`PA194ActualLoopOrbit`, `PA194ModelLoopCost`, `PA194ModelLoopCostInputs`,
`PA194ActualLoopCostInputs`, `PA194ActualLoopNextFrame`,
`PA194ActualLoopOneStep`, `PA194ActualPhysicalIteration`,
`PA194Site27ClockDirect`, `PA194Site28DynamicClock`, `PA194Site28ClockCode`,
`PA194Site29DynamicClock`, `PA194Site29ClockCode`,
`PA194ActualLoopExactStep`, and `PA194ActualPhysicalOrbit`. The earlier shared
controller/physical source modules and every audited theorem are specified in
the checker. The seven new exact-clock and physical-orbit theorem audits show
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

Successful invocation, from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-actual-physical-orbit.sh "$PWD" \
  /dev/shm/pa194-model-length /dev/shm/pa194-source-controller \
  /dev/shm/pa194-source-physical /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-site28-controller /dev/shm/pa194-site28-work/build-complete \
  /dev/shm/pa194-site28-work/build-finish-return \
  /dev/shm/pa194-site28-work/build-site29-selected-return \
  /dev/shm/pa194-site28-work/build-carry-seven \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-codes \
  /dev/shm/pa194-site28-work/build-site29-to-increment \
  /dev/shm/pa194-site28-work/build-site29-return-to-root \
  /dev/shm/pa194-site28-work/build-site29-path30-identities \
  /dev/shm/pa194-site28-work/build-site29-complete \
  /dev/shm/pa194-site28-work/build-site28-dynamic-complete \
  /dev/shm/pa194-site28-work/build-site29-dynamic-complete \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-site30-jump \
  /dev/shm/pa194-site28-dynamic-controller \
  /dev/shm/pa194-site29-dynamic-controller Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
```
