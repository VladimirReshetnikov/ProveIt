# Exact survivor corridors

Report 24's optional reducers preserve the full differential after scalar
cancellation. `corridor` removes graph paths that cannot connect scalar
survivors, then chooses forward or reverse propagation per weak component.
`corridor-adaptive` first permits `max(256, 4 * live_objects)` sparse Schur
update pairs, retaining completed pivots before switching to full transfer.
This is a work heuristic, without an introsort-style worst-case guarantee.

From `fast/`:

```sh
python -B -m fastunknot khovanov examples/conway.json --reduction corridor --check-d2
python -B -m fastunknot recognize examples/conway.json --reduction corridor-adaptive --seconds 30
python -B -m unittest discover -s tests -v
python -B corridor_research/audit_corridor.py --output /tmp/corridor-audit.json
python -B corridor_research/audit_graded_support.py --output /tmp/support-audit.json
python -B corridor_research/audit_scalar_representation.py --output /tmp/scalar-audit.json
python -B corridor_research/benchmark_corridor.py --output /tmp/corridor-timing.json
python -B corridor_research/verify_archive.py --output /tmp/corridor-archive.json
```

The archive verifier requires a new output filename, verifies all 20 entries
in the delivered integration manifest, and runs its suites and audits in a
temporary copy. The advertised package-wide `SHA256_MANIFEST.json` is absent;
the recorded provenance claim is therefore limited to the available manifest.
The delivered report is preserved unchanged.

Both public policies require the standard backend, minimum-fill pivots,
bit coefficients, `self_inverse=True`, `race=1`, and no window truncation.
They support the component coefficient engines and existing tail contraction.
The raw API raises resource errors; recognition returns `UNKNOWN`. Replacement
allocation and a final deadline check precede installing any new differential.
Coefficient caches may be populated during an unsuccessful transfer.

Direct controls expose the setup/performance tradeoff:

```python
from fastunknot.corridor import CorridorScan

scan = CorridorScan(mode="auto", prune=True,
                    direction_policy="ports", scalar_engine="components",
                    max_objects=50000)
# Feed crossings of a validated nonempty diagram in the chosen order.
```

`mode` is `forward`, `reverse`, or `auto`. `direction_policy="reach"`, the
public default, compares exact structural bounds computed from packed endpoint
sets. `"ports"` uses Boolean reachability and chooses the side with fewer ports.
`scalar_engine="global"`, the public default, uses the existing packed binary
contraction. `"components"` contracts scalar graph components on local indices
and returns sparse index columns, with the same scalar basis and coefficients.
The stronger support-only reference is in `fastunknot.graded`; its similarly
named classes are separate from the public full-transfer `graded` policies.

The shared-suffix family has `R(1+2M)` radical-edge attempts in forward mode
and `R+2M` in reverse. With odd `M` the output remains nonzero. The sparse
scalar/port policy gives a complete near-linear stage at fixed algebra size,
including setup. This is a constructed homogeneous complex; realization as
knot prefixes is unproved, and ordinary sparse cancellation handles it well.

Evidence is retained in `../synthesis/data/corridor-*` and
`results/corridor_integrated_20261008.json`. The benchmark uses 11 arms,
seven shuffled paired warm rounds, fresh states and a standard A/A control.
Actual timings include scanner construction and all reduction work but exclude
diagram construction and shared order selection; synthetic timings exclude
fixture construction. Every result is checked outside timing. Coefficient
propagations, actual compositions and elapsed time are distinct metrics.

The full maintained suite passes 458 tests. The independent audit checks 3,885
entrywise transfers at 555 prefixes of 80 diagrams, with eight contraction
identities per prefix. The graded support shortcut adds zero successes over the
degree-gap shortcut in 639 stages of 72 diagrams. The theory and complete cost
accounting are in [the article section](../../synthesis/corridor_transfer.tex).
No unrestricted quasi-polynomial complexity or default-policy change follows.

In the maintained run, eager corridor transfer is 2.0–9.5 times slower on
all six actual scans; adaptive makes no switches, with standard/adaptive
ratios 0.808–0.938 (A/A 0.986–1.019). The sparse refinement also loses on
all six. The size-255 shared-suffix case gains 18.14 times over the current
forward transfer, but is 6.49 times slower than ordinary sparse cancellation.
On the constructed dense dead-branch case, eager and adaptive corridor gain
1.406 and 1.380 times over sparse cancellation. These are complete stage
measurements on constructed complexes, not measured knot-recognition gains.
