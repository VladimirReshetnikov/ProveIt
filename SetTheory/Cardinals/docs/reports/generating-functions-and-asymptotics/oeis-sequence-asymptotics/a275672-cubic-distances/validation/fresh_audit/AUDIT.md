# Additional source audit and independent differential checks

Date: 2026-10-08 UTC.

## Verdict and scope

No correctness defect was found in the two frozen search sources that would
invalidate the reported exhaustive upper-bound runs for `n=7, target=11`
or `n=8, target=13`. The diameter case split, remaining symmetry reductions,
largest-edge prefix, dynamic compatibility search, and arithmetic pruning
are sound under their stated invariants, and the inspected code maintains
those invariants.

This conclusion comes from a separate mathematical/source audit, small
independent differential tests, and arithmetic/run-record consistency
checks. It is **not** verification by a formal proof-certificate checker,
and the full `n=7` and `n=8` UNSAT searches were **not** rerun as part of this
audit. The large computations still rely on the supplied search
implementation, compiler, and recorded execution. The corroborating
large runs share a kernel and should not be described as independent
implementations.

A separate review of `rainbow_prefix_filtered.cpp` found its added prefix
filters sound, including their interaction with the active stabilizer.
This prototype is distinguished below from the frozen proof sources.

## Reviewed source identities

The SHA-256 digests of the sources actually included in the differential
test builds were unchanged when checked after the tests:

| Source | SHA-256 |
|---|---|
| `reviewed_sources/rainbow_exact_v5.cpp` | `d3c14a9fb6e6b1b67f0060ae67244370aacd4ae905cb33dd84fa62808840541d` |
| `reviewed_sources/rainbow_edge_prefix.cpp` | `321fd408db85b0e91543dbac68838d784fd8ee16032aabfc52d4d6b2939ca64d` |
| `reviewed_sources/rainbow_prefix_filtered.cpp` | `43928be3b2fcb6a2e5d740f1cc80d6c11472bc89dbc606c9b3200c61f3f476f4` |

`release/EXACT_SEARCH.md` was read in full. All 36 file hashes listed in
the release manifest matched the files present at audit time. None of
the release files was edited during this audit.

## Mathematical and implementation findings

### 1. Diameter symmetry is complete

For `K=target*(target-1)/2`, a solution requires `K` distinct attainable
positive squared distances, so its largest distance is at least the
`K`th smallest attainable value. The source uses the correct zero-based
index, `K-1`.

`pair_representative` enumerates all coordinate permutations and all
independent coordinate reflections, orders the two endpoints, and takes
the least pair. Point IDs use the same lexicographic order as coordinate
triples. Consequently, the outer pair loop retains one representative
of every possible diameter orbit. The initial candidate restrictions
are exactly the individual restrictions imposed by the fixed unique
diameter edge.

An independent Python check computed orbits by closing pairs under three
generators: exchanging two coordinates, cycling coordinates, and
reflecting one coordinate. This does not reuse the C++ loop over 48
transformations. It reproduced every logged representative, not just the
number of orbits.

| Instance | Attainable positive distances | Diameter threshold | Eligible unordered pairs | Diameter orbits |
|---|---:|---:|---:|---:|
| `n=7, target=11` | 66 | 68 | 810 | 31 |
| `n=8, target=13` | 87 | 101 | 660 | 23 |

### 2. Residual point symmetry does not lose a completion

Let `H` be the setwise stabilizer of the fixed diameter. The initial
candidate set is invariant under `H`. Choose an `H`-image of a completion
whose sorted remaining point list is least, and let its first point be
`r`. Then `r` is least in its own `H`-orbit, and every other remaining
point has orbit minimum at least `r`. Otherwise applying an element of
`H` would produce a completion with a smaller first point.

These are exactly the restrictions imposed by `search_diameter`.
Changing the minimum stabilizer size at which the reduction is applied
from four to two only changes how often a valid reduction is used.
The positive witnesses do not depend on the optional anchor-mode
symmetry argument, and the published upper bounds use diameter modes.

### 3. The longest-edge prefix is exhaustive

If `b_1 > ... > b_K` are the chosen distances in decreasing order, then
`b_r >= d_(K-r+1)`. In `extend_edge_prefix`, `rank=processed.count()+1`
and `distance_values[K-rank]` therefore give the correct lower bound.

The scan through already used but unprocessed distances raises this
bound to the greatest such distance when necessary. This ensures that
an existing selected edge cannot be skipped in the claimed decreasing
prefix. The subsequent complete recomputation of selected distances
also rejects any unprocessed selected edge longer than the proposed
next edge.

The pair pool is the union of selected points and individually
admissible candidates. Its enumeration includes both new endpoints,
one new endpoint, and two already selected endpoints. The last case is
essential and is present. `processed` can safely identify earlier edges
by their distances because every selected-set distance is checked for
uniqueness and all endpoints of previously processed edges remain
selected.

At each level the active maps fix every earlier processed edge setwise.
They form the required subgroup. They preserve the selected set, used
distances, candidate set, and edge admissibility. Taking the least
next-edge pair under this subgroup is consequently complete.

The special handling of the second edge exempts only the original
diameter pair from the second-edge bound. This is correct because the
selected list begins with the original two endpoints. The general
prefix routine uses the processed-distance mask instead.

`max_distance` is global, but the prefix routines set it to the proper
current bound immediately before entering ordinary search; intermediate
prefix checks use their explicit length arguments. No dependence on a
stale global bound was found. Early acceptance when the selected set
already has the target size is valid because the complete selected set
has already passed the distance-uniqueness checks.

### 4. Compatibility, coloring, and core pruning are sound

The selected-distance mask `U` contains every selected-selected
distance. Each candidate radial mask has one distinct distance to each
selected point and is disjoint from `U`.

The adjacency test checks every possible distance collision involving
two candidates and the selected set. On selecting `v`, each surviving
candidate's radial mask is extended by its distance to `v`; adjacency
guarantees that this preserves the invariant. Collisions between edges
whose endpoints are all initially candidates are detected as endpoints
are selected and compatibility is rebuilt. A current compatibility
clique is used only as a necessary condition, not as a sufficient
condition for a full distinct-distance set.

Each greedy color class is an independent set. Reverse traversal of the
color order removes previously considered vertices from `active`, so
the stored color bound applies to the exact remaining prefix. In the
prefix source, iteratively deleting vertices of degree below `need-1`
cannot delete any vertex of a `need`-clique. Deleted vertices are
excluded from both coloring and branching. Retaining their distances
in an earlier capacity calculation only weakens pruning.

### 5. Capacity and occupancy filters are necessary conditions

Every completion needs `selected.size()*need` distinct radial distances.
Its full distance set is contained in `used`, the union of radial masks,
and distances of compatible candidate pairs. The corresponding union
cardinality test is therefore safe.

Squared distance modulo four equals the number of differing coordinate
parity bits. The occupancy requirement formulas are correct, including
the within-class contribution to residue zero. The four residue masks
also align correctly across 64-bit words because 64 is divisible by
four. Passing only parent-feasible occupancy IDs to a child cannot
exclude a valid completion of that child: such a completion would also
have passed all its ancestors' necessary conditions.

An independent stars-and-bars enumeration reproduced 2,376 globally
feasible occupancy vectors for `n=7, target=11`, with residue capacities
`[18,21,18,9]`, and found 2,952 for `n=8, target=13`, with capacities
`[18,26,28,15]`.

For the later filtered prototype, `used` union all attainable distances
at most the current prefix cap still contains every possible completion
distance. The radial count and coordinate-parity class count tests are
necessary. The permitted occupancy subset remains invariant under the
active stabilizer: each ancestor's filter is invariant under that
ancestor's stabilizer, and the current stabilizer is a subgroup of each
ancestor's. Resetting from `global_occupancies` for each diameter case
prevents filtering from one case contaminating another. No defect was
found in this extension.

### 6. Fixed storage and control flow

For `1 <= n <= 10`, there are at most 1,000 lattice points and all squared
distances are at most 243. The 1,024-bit vertex sets and 256-bit distance
masks are large enough. Candidate sets contain distinct unselected
points. Bit scans are only performed on nonzero words, and bit shifts
have counts below 64. Targets 11 and 13 are far inside the safe integer
range for every arithmetic operation inspected.

Timeout propagation is conservative for the mathematical conclusion:
once detected, it propagates as `UNKNOWN`, not `UNSAT`. Some outer work
checks the clock only intermittently, so the time limit is not a strict
wall-clock deadline. That can extend runtime but does not create a
false exhaustive result.

## Differential tests actually performed

`differential_audit.cpp` includes each reviewed source unchanged, renaming
its `main` function, and calls its search functions. The separate oracle
enumerates subsets of the candidate pool in increasing index order. It
recomputes squared distances directly from coordinates and maintains a
256-entry byte ledger. It uses no clique graph, coloring, core,
symmetry, parity, or occupancy pruning. Every returned witness is also
checked against that ledger and the permitted points.

Each implementation received the same deterministic test suite:

* 1,800 restricted random states for side lengths 2, 3, 4, 5, 7, 8, and
  10, including caps below some already selected distances.
* Six larger candidate states, reaching 999 candidates and exercising
  all 16 vertex-mask words.
* 96 states derived from the supplied ten-point and twelve-point
  witnesses, with additional candidates, using targets 10, 11, 12, and
  13.
* Every eligible unordered diameter pair for `(n,target)` equal to
  `(2,3)`, `(3,3)`, `(3,4)`, `(4,5)`, and `(4,6)`: 927 pairs in total.
* For each of those 927 pairs, prefix depths 2 through 6 in each prefix
  implementation: 4,635 additional comparisons per prefix source.

| Implementation | Kernel comparisons | Kernel SAT / UNSAT | Diameter comparisons | Prefix comparisons | Result |
|---|---:|---:|---:|---:|---|
| Frozen v5 | 1,902 | 1,326 / 576 | 927 | 0 | All agree |
| Frozen edge prefix | 1,902 | 1,326 / 576 | 927 | 4,635 | All agree |
| Filtered prototype | 1,902 | 1,326 / 576 | 927 | 4,635 | All agree |

Each oracle execution visited 81,557 recursion nodes. The builds used
GCC 13.3.0 with AddressSanitizer and UndefinedBehaviorSanitizer; successful
runs produced no sanitizer diagnostics. Leak detection was disabled
because LeakSanitizer reported it could not operate under this
environment's tracing. Equivalent commands, from this portable `fresh_audit` directory:

```sh
g++ -O1 -g -std=c++17 -fsanitize=address,undefined -fno-omit-frame-pointer -DAUDIT_IMPL=0 differential_audit.cpp -o differential_audit_0
ASAN_OPTIONS=detect_leaks=0 ./differential_audit_0
g++ -O1 -g -std=c++17 -fsanitize=address,undefined -fno-omit-frame-pointer -DAUDIT_IMPL=1 differential_audit.cpp -o differential_audit_1
ASAN_OPTIONS=detect_leaks=0 ./differential_audit_1
g++ -O1 -g -std=c++17 -fsanitize=address,undefined -fno-omit-frame-pointer -DAUDIT_IMPL=2 differential_audit.cpp -o differential_audit_2
ASAN_OPTIONS=detect_leaks=0 ./differential_audit_2
python structural_audit.py /path/to/frozen_release
```

The compiler warning about the renamed, unused `reviewed_program_main`
reaching its end results from the harness renaming C++'s special `main`
function. It is not a warning about the original program's `main`, and
the renamed function is never called by the tests.

The JSON outputs are saved as `differential_audit_0.json`,
`differential_audit_1.json`, `differential_audit_2.json`, and
`structural_audit.json`. The latter also confirms that both witness
files have distinct in-range integer points and respectively 45 and 66
different squared distances, and that every expected large-run case is
logged as UNSAT with the final node count matching its JSON record.

## Concrete limitation outside the claimed instances

The command-line parser accepts arbitrarily large positive `target`
integers, but computes `target*(target-1)` in signed `int` before applying
the global distance-count bound. Sufficiently large accepted inputs can
therefore overflow; for example, `target=46342` already exceeds the
32-bit multiplication range. Robust general-purpose input handling
should first reject targets larger than the number of lattice points
and/or compute the pair count in a wider type.

This input-validation defect does not apply to the reported targets 11
and 13, the tested targets, or any ordinary feasible target for the
supported boxes. The release files were deliberately left unchanged.

No finite collection of differential tests proves that a program is
correct on all inputs. These checks add evidence for the implementation
and exercise the specific reductions at issue; the full large-instance
upper bounds remain reproducible exhaustive-computation claims rather
than formally checked proof certificates.

## Portable package and replay

This directory contains no executable binaries. The three reviewed source
snapshots in `reviewed_sources` are byte-for-byte copies of the files
identified above. The differential harness differs from the original audit
harness only in its include paths. The structural script now accepts the
frozen release folder as a positional argument; its mathematical checks
are unchanged. Recorded JSON summaries and empty runtime diagnostic files
are included. The frozen release itself is supplied separately.

`run_checks.py` rebuilds in a temporary directory, runs all three differential
suites, and checks their summaries against the recorded JSON. The optional
release argument also replays the structural checks:

```sh
python run_checks.py --release-root /path/to/frozen_release
ASAN_OPTIONS=detect_leaks=0 python run_checks.py --sanitize --release-root /path/to/frozen_release
```

The supplied SHA-256 manifest identifies the portable audit artifacts.
Its hashes establish file identity and integrity; they do not turn the
recorded computations into formal proof certificates.
