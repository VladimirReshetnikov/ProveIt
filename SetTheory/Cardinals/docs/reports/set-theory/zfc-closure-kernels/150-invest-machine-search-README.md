# Independent machine-side continuation packet

**Status: no 217-state blank-tape construction has been certified by this packet.** The positive artifact here is a new, independently checked 218-state alternate of the incoming contextual K218 table. The other artifacts document reproducible searches and a broader configuration relation for future searches.

The parent report should distinguish these findings from its separate 217-state initialized core. An initialized computation is not a standard blank-tape Busy Beaver candidate.

## What was added

The strongest new search synthesizes **both** outgoing rows of a merged state, independently, and permits execution to revisit that modified state. Earlier one-common-row searches and fixed helper-path catalogs cover narrower families. A demand-driven search requests a row only when a concrete local trajectory reads it. A failure before that read eliminates every possible completion of that row. C++ implementation and adaptive ordering make this practical.

For each old 218-state table and chosen pair, a prospective 217-state table has 217 working-state targets plus the halt target. Each new row therefore has `2 × 2 × 218 = 872` choices, and a pair of rows has `760,384` complete assignments. A report's “complete assignments rejected” count includes whole subtrees pruned after partial assignments; it is **not** a count of separately simulated complete tables.

The first completed family consists of 2,408 unordered pairs of pure right-moving decoder states with opposite uniquely written incoming markers. It covers 1,831,004,672 complete assignments on each of three domains, with no survivor:

| Domain | Radius / fuel | Partial checks | Complete assignments covered |
|---|---:|---:|---:|
| Inductive all-initial-tape domain | 7 / 97 | 43,586,712 | 1,831,004,672 |
| Complete primitive frames, constant-one spare tail, and exact startup | 9 / 197 | 48,989,624 | 1,831,004,672 |
| As above, additionally respecting actual source register masks | 9 / 197 | 48,989,624 | 1,831,004,672 |

The latter two domains are **finite discovery samples**, not inductive binary-window certificates. A survivor there would require an unbounded proof. Domain counts and candidate families overlap, and should not be added as counts of distinct machines.

The wider family also completed: **all 23,653 unordered working-state pairs**, without any marker or decoder restriction. Both domains returned zero survivors. Each row below covers 17,985,362,752 complete assignments:

| Domain | Partial checks on completed pairs | Elapsed time |
|---|---:|---:|
| Inductive all-initial-tape domain, radius 7 / fuel 97 | 578,694,189 | 180 seconds plus a 50.6-second resume |
| Source-mask / constant-one-spare / exact-startup finite domain, radius 9 / fuel 197 | 747,494,205 | 308.8 seconds |

The first run restarted its last incomplete pair. The combined receipt has exactly one completed row for each of the 23,653 pairs; the abandoned partial attempt is recorded separately and excluded from the counts above. The full tables, input hashes and per-pair counts are in `results/twoaction_allpairs_*`.

An additional C++ search used the complemented-entry-marker relation on all **4,886 ordered pairs of same-marker pure decoder states**. It covered 3,715,236,224 complete assignments with 29,123,582 partial checks in 10.8 seconds, with zero survivors. This family and the earlier 96-pair complemented-marker family overlap in 48 pairs; their counts should not be added as distinct machines.

## Other completed searches

| Family | Count | Outcome |
|---|---:|---|
| Incoming K218 inherited/one-common-row folds | 642,320 | No survivor |
| Incoming row157 alternate, same family | 640,584 | No survivor |
| Public single-row rewrites | 381,500 | 463 local diagram passes; no graph-state reduction |
| Incoming single-row rewrites | 381,500 | 472 local diagram passes; no graph-state reduction |
| Public common-row fold plus one individually admissible extra-row rewrite | 5,701,222 | No survivor |
| Complemented-marker folds with inherited/common-row choices | 462,067 | No survivor |
| Complemented-marker folds, arbitrary two new rows on 96 ordered eligible pairs | 72,996,864 complete assignments, covered by 304,424 partial checks | No survivor |
| Source-mask, constant-one-spare and startup ordinary fold discovery | 322,028 | No survivor |

The preserved-bit/left-moving complemented-marker subfamily is also recorded: 4,562,304 assignments covered by 46,530 partial checks. It is included in the broader arbitrary-two-row complemented-marker family and is not an additional disjoint count. The extra-row family similarly includes the earlier marker-limited experiment.

All finite-window rejection counts mean that the specified bounded positive-block diagram was not found. They are neither semantic counterexamples nor state lower bounds.

## Checked positive artifact

The supplied incoming table has SHA256:

`3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1`.

Changing exactly

```text
157 1 1 L 148
```

to

```text
157 1 1 L 187
```

gives `data/incoming-row157.native.tm`, SHA256:

`02ec4a475115217cd836f755e2806ba65a842a6377d13c7975a8ec81045819a5`.

The unchanged independently authored `check_joint_fold.py` recomputed 1,001,257 inductive contexts and checked 1,280 nontrivial contexts. Maximum old/new block lengths were 2 and 3. Its intentionally corrupted initial-halt control was rejected. The proof establishes relative all-initial-tape halting equivalence to the incoming K218 table. It does not independently reconstruct that table's theory-to-machine calibration.

## Source-mask evidence

For the exact public K218 source, the inherited bucket invariant generator was rerun and its output independently checked against the exact 312,909-step blank startup. The checker performed 32,072 closure checks. It finds 4,741 overapproximated reachable sites, with unreachable sites 4607, 4719, and 4720. The always-zero decrement guards are at sites 4606 and 4718.

Eight mask-respecting register scenarios at each allowed primitive guard, with one through five constant-one spare blocks, produced 49,296 complete primitive cases, 29,164,044 concrete steps, and 225,840 radius-nine contexts before adding startup. All 218 working states and all 436 read-rows occurred after startup was added. These sample contexts justify a discovery filter only. The independent source bucket invariant itself is universal, but lifting it to an inductive binary-window invariant is a separate obligation.

## Reproduction

Python 3.10+ and a C++17 compiler suffice. No third-party Python package is required. Every output directory must be fresh. `--repo` accepts a ProveIt checkout or its `Computability/BusyBeaver/Research/ZFC` directory.

```sh
python run.py --mode control --output /tmp/k218-control
python run.py --mode marker-control --output /tmp/k218-marker-control
python run.py --mode incoming-variant --output /tmp/k218-incoming-variant
python run.py --repo /path/to/ProveIt --mode allinitial --pairs opposite --output /tmp/k218-twoaction
python run.py --repo /path/to/ProveIt --mode masked --pairs opposite --output /tmp/k218-masked
python run.py --repo /path/to/ProveIt --mode masked --pairs all --seconds 600 --output /tmp/k218-allpairs
python run.py --repo /path/to/ProveIt --mode complemented --pairs same --output /tmp/k218-complemented
```

The synthetic six-to-five-state control is intentionally stopped at its first survivor. It is independently certified; an initial-halt corruption is rejected. Its `HIT_OR_INCOMPLETE_LIMIT` search status is expected and is not a failed proof.

The separate eight-to-seven-state marker control has all eight old states syntactically reachable. Its merge writes a temporary 1 marker on entry, uses the previous tape cell to select one of two continuations, and restores the marker to 0 before joining the ordinary relation. A separately written represented-configuration checker proves all 502 invariant contexts, with 128 nontrivial one-old-step/three-new-step diagrams, and rejects the initial-halt corruption. These small synthetic tables exercise the search/checker mechanisms; neither is related to ZFC.

Additional exploratory families are directly reproducible:

```sh
python code/search_incoming.py --seed data/incoming-k218.native.tm --output /tmp/k218-incoming-search --seconds 110
python code/search_incoming.py --seed data/incoming-row157.native.tm --output /tmp/k218-incoming-row157-search --seconds 110
python code/flipped_fullactions.py --repo /path/to/ProveIt --output /tmp/k218-flipped
python code/extra_general_merge.py --repo /path/to/ProveIt --output /tmp/k218-extra-row
```

Historical JSON receipts retain original execution paths where those paths were recorded as provenance. Reproduction scripts have configurable repository and output locations; they do not require the original workspace. The one-row result catalogs are included as data for the extra-row search. Their positive outcomes are discovery results and were not separately promoted to independently certified tables.

## Complemented-marker relation

`RESEARCH_NOTE.md` explains the relation in detail. The old removed state can be represented by the surviving state with one nearby bit complemented. Incoming transitions establish the temporary marker by changing their written bit, without allocating a new state. The merged continuation must consume or restore that marker before returning to the ordinary relation. This expands the tested family beyond same-tape and fixed-head-offset quotients. No successful K217 instance was found in the tested specialization.

For any future positive instance, independently prove the relation and its initial-state condition, use positive finite blocks on both sides, and verify that every matched endpoint satisfies the representation. A bounded search's own acceptance routine is not a substitute for that proof.
