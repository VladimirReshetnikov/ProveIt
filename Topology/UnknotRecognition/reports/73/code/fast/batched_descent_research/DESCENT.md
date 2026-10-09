# A complete, bounded collapse-only research driver

`descend.py` accepts a JSON object with exactly `triangulation` and `heights`.
The triangulation must satisfy the maintained finite-manifold validator and
have at most two interior vertices. The heights must define a coherent
integer cocycle. Integer fields may use the repository's signed hexadecimal
encoding when large. Local additive height constants are normalized away;
source binding records the triangulation and the resulting cochain.

From `code/fast` in the delivered package:

```sh
python -S batched_descent_research/descend.py supplied.json \
  --output trajectory.json --max-rounds 25 --max-work 10000000 --disk-count
python -S batched_descent_research/descend.py supplied.json --replay trajectory.json
python -S -m unittest discover -s tests -p test_batched_descent_driver.py -v
```

The output includes its own `source` object, so an artifact can also be
replayed in isolation with:

```sh
python -S batched_descent_research/descend.py trajectory.json --replay trajectory.json
```

For integration with an external source, use the original supplied JSON in
the replay command; this binds the proof to the intended input instead of
merely accepting the source packaged with the proof. A source is a finite
triangulation/cochain pair. The driver does not create a separate correspondence
to a knot diagram or a meridional marking.

Each round obtains the complete current legal 3--2 census, greedily chooses
a maximal family of disjoint regions, and runs `state.optimal_subbatch` on
that fixed family. The latter maximizes peeled Euler gain, retaining as
many collapses as possible among ties. Each committed batch is independently
verified for finite geometry, coherent transport, and its nonnegative
peeled-Euler gain before being retained in the chain. At most two interior
vertices suffice for the exact standard-library small-cover matching solver.
No optional matching package is needed for this driver.

The only trajectory statuses are:

* `STALLED`: the producer found an empty legal census or an empty optimal
  subbatch of its chosen greedy packing.
* `ROUND_LIMIT`: the cap on committed batches was reached. The driver has
  not performed an additional terminal census, even if the endpoint would
  in fact stall on the next round.

Omitting `--max-rounds` permits the complete collapse-only policy to run until
it stalls; the tetrahedron count decreases at every committed batch.
`max_rounds=0` validates and returns the source without a census. The work
limit counts callback ticks, including verification, rather than arithmetic
bit operations or elapsed seconds. Work exhaustion raises `CocycleLimit`;
arbitrary caller cancellation exceptions also propagate. Interrupted private
states are discarded. The CLI writes atomically only after a result is
complete, so cancellation does not overwrite an earlier output with a partial
trajectory. Keeping every intermediate triangulation can require quadratic
space over a full trajectory.

The independent `verify_descent_chain(triangulation, heights, certificate)`
consumer checks the initial source, every nonempty commuting batch and its
score, and the final endpoint. It does not rerun the candidate generator,
selector, or descent producer. Counts in `round_diagnostics`, producer
optimality, and the operational `STALLED` claim are outside that proof
contract. In particular, a stalled state is not a certificate of surface
absence or a knot verdict.

With `--disk-count`, the endpoint is passed to
`normal_compressing_disk_count(record_certificate=True)` using the normal
coordinates of the actual final coherent heights. A completed count is
independently verified and its native certificate is embedded in the chain.
`--max-disk-cycles` may instead yield an `INCONCLUSIVE` endpoint count and no
disc certificate; this does not change the trajectory status. A completed
count concerns only compressing-disc components of that supplied surface.
Neither a positive nor a zero count is promoted to an unknot decision.

All paths are resolved relative to `code/fast`; the driver and its independent
replay use Python's standard library and the included `fastunknot` modules.
They do not require network access or third-party numerical libraries.
