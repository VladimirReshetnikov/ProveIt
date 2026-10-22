# K215 runtime proof: share the decoder prefix, check the residual

Pinned repository: `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Contribution

The maintained proof already has a checked theorem taking every source walk
to its exact decoder leaf port, uniformly over the gap and the register
contents. The `sharing-interfaces` proposal had residual checker definitions
but no compiled connection to coverage. The separate `semantic-coverage`
proposal had a compiled consumer interface but replaced no concrete checks.

This packet joins those two pieces. `KResidual215` computes the leaf control
state from the complete certified role path; its correctness follows from
the maintained `RoutedEntry` witness, rather than an external lookup audit.
The old symbolic evaluator then checks only execution from that exact port
to the existing full successor configuration. All nine existing subtree
partitions are retained, including both guarded executions of every
decrement. `KResidualSites215` derives semantic coverage and the concrete
two-way register-machine/Turing-machine simulation.

The exact source program, literal table, register interpretation, `KSim.Rel`,
target configurations, terminal-state premise and positive-progress
requirement are preserved. The successful compiler records in `evidence/`
and the summary in `result.json` state the completed verification scope.
The unchanged `KZip.lean` emits one pre-existing unused-simp-argument linter
warning. The new bridge, residual batches, facade and typed audit emit no
warnings; the complete printed axiom union is `propext`, `Classical.choice`
and `Quot.sound`.

## Mathematical contract

`Prefix M Q input` means that for every natural gap `n` and every register
list `vs`, the physical configuration interpreting `start Q` reaches the
physical interpretation of `input`. This prefix may have zero duration.

`runFrom_sound` turns an accepted residual check into a **positive** physical
run, under the original register validity predicate. Its executor starts
with progress `false`. Therefore `Reach.trans_reach1` composes the shared
prefix with a positive suffix. This is what preserves the well-founded
backward halting argument; setting the initial progress flag to true would
not justify that argument.

`checkFrom_contract` supplies the inherited semantic `EdgeContract` for all
five leaf constructors. It keeps both zero/nonzero decrement guards, the
path-length limit, register-index limits, exact overflow flags and full
successor paths. Halting uses the same state-230 terminal premise.

`portState_of_entry` proves that following the role graph computes the
state from the source-directed `RoutedEntry` theorem. `walk_contract` then
uses the maintained `walk_prefix`, including implicit zero padding and the
entire consumed program-counter word. The surrounding arbitrary gap and
register frame are never erased or replaced by finite test values.

Finally, `covered_of_residual` applies the existing finite tree coverage
theorem to recover all source walks. The inherited semantic simulator
provides both halting directions. This does not assume completeness of the
old fuel-limited Boolean checker and does not claim that residual acceptance
implies acceptance by that old checker.

## Scope and integration

The packet includes the inherited semantic `KSim` proposal as a prerequisite
overlay; its baseline is byte-identical to the pinned maintained `KSim`.
All other borrowed modules are current pinned sources. The new checker
bridge, residual subtree proofs and typed audit are this packet's work.
`sources.json` identifies every input and its provenance. The original
source/tree partition producer is credited in the adapted sources.

The exact *full ZFC endpoint* has not been rebuilt by this focused runtime
check. The register-engine `BoxLemmas` and terminal premise retain their
original roles as hypotheses of the runtime theorem. The existing machine
instantiation supplies those premises elsewhere. Initialization, dense
table conversion, program/calculus equivalence and the set-theoretic lower
and upper chains are outside this fresh scope.

`integration/endpoint-UNCHECKED.patch` gives the explicit next connection:
add a semantic variant of the existing generic endpoint composition, and
have `KEndpoint215` consume the new semantic coverage. It preserves the
public halting/nonhalting statements. It is supplied as an **uncompiled
integration proposal**, separate from the checked runtime patch; rebuild
the affected complete endpoint and typed endpoint clients before adopting
that endpoint change.

This replaces repeated decoder simulation with one reusable semantic theorem. The added generic
interfaces and proof bridge increase source text. The alternative site
module names retain the old route for compatibility. No net source-size
reduction or controlled wall-clock speedup is claimed for the runtime
packet. The exact source deltas and successful local compiler times are
reported separately in `metrics.json`; lock waiting is not compilation.

For a like-for-like replacement footprint, the original `KSim` plus its ten
site files occupy 86,896 bytes / 1,321 lines. The semantic `KSim`, new bridge,
and ten residual site files occupy 103,551 bytes / 1,651 lines: **16,655 more
bytes and 330 more lines**, excluding the 44-line typed audit. The delivered
alternative module names also preserve the old site route, so this comparison
is not a claim that any old repository files have been deleted.

## Replay

No network or compiled proof objects are required. Use a new output directory:

```sh
python3 replay.py --lean /path/to/lean-4.32.0-linux/bin/lean --out /tmp/k215-residual-replay
```

To bind unchanged inputs to a local pinned ProveIt checkout, add
`--repo /path/to/ProveIt`. Their hashes must match; changed inputs are not
silently accepted. `--scope bridge` checks only the focused generic/decoder
bridge and its dependencies, omitting concrete all-site replay. The default
`--scope sites` also checks all nine batches, their final composition and
the typed/counting audit. All compiler calls run sequentially under the
repository's shared build lock, and all output objects are new.

The site producer is also portable. This regenerates the ten residual site
files from the unchanged upstream partition; all ten outputs were reproduced
byte for byte in the supplied `regeneration.json` check:

```sh
python3 adapt_sites.py --repo /path/to/ProveIt --out /tmp/k215-residual-generated
```

The driver checks successful return codes and printed axiom profiles,
recording source hashes, direct dependency object hashes, output hashes,
compiler identity, logs, compilation time and lock wait separately. Compiler
failure stops the replay. Historical failed syntax/dependency attempts are
retained separately from the successful records; they are not evidence for
the final theorem.

## Further opportunities

After endpoint integration, factor generic `runFrom`/`checkFrom` into the
shared checker interface and make the original entry checker a wrapper.
This can remove small duplicated proof bodies while preserving old APIs.
Next replace a complete repeated residual family by a reusable primitive
contract through the same semantic interface. Measure that family against
the all-residual baseline with identical toolchain and hardware; reductions
in abstract step count alone do not establish a wall-clock speedup.
