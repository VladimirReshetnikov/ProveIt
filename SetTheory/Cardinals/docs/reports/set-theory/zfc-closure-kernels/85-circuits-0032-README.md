# Synthesizing the unshared row of a state fusion

This experiment found **no 245-state survivor** in the family described below.
It extends the older row-provider fusion searches: after identifying two states
whose quotient transition tables share exactly one row, the other row is
synthesized as every binary write, left/right move, and surviving-state or halt
target. The results are finite instruction-fixture searches, not an impossibility
theorem for 245-state machines or an unbounded simulation certificate.

## Exact search family

For each unordered pair of working states `{a,b}`, with `a<b`, let `pi(b)=a`
and let `pi` fix all other states. Apply `pi` to the target of each transition.
Retain the pair precisely when the resulting rows for `a` and `b` agree on
exactly one read symbol. Keep that common row. On the other read symbol, try
all actions

```
(write, direction, target) in {0,1} x {L,R} x ((Q - {b}) union {halt}) .
```

The candidate removes `b` and redirects every surviving transition targeting
`b` to `a`. Dispatcher 96 and blank-start state 95 are redirected if necessary.
Each pair contributes `2 * 2 * 246 = 984` recipes. The converse orientation is
isomorphic under state renaming. Pairs sharing neither row, and pairs sharing
both rows, are outside this family. No additional row edits or register
renamings are synthesized.

| Layout | Eligible pairs | Recipes | Survivors, all 8,391 | Survivors, 8,385 guards | Survivors, 33,540 product fixtures |
| --- | ---: | ---: | ---: | ---: | ---: |
| Baseline Context246 | 352 | 346,368 | 0 | 0 | 0 |
| 0 | 352 | 346,368 | 0 | 0 | 0 |
| 233 | 353 | 347,352 | 0 | 0 | 0 |
| 235 | 351 | 345,384 | 0 | 0 | 0 |
| 236 | 352 | 346,368 | 0 | 0 | 0 |
| 237 | 352 | 346,368 | 0 | 0 | 0 |
| **Total per fixture domain** | **2,112** | **2,078,208** | **0** | **0** | **0** |

The same recipe sets were screened against three domains. They must not be
counted as three disjoint sets of synthesized machines.

## Fixture domains and their logical limits

`--scope all` uses one concrete register vector for each of the 8,391 guarded
source instructions. The physical primary values are `[1,4,2,0,3,1,4,2,0]`,
except that the decremented primary is replaced by zero or two to select its
guard. There are two spare registers, with values zero and two. The initial
head is zero, the header distance is 40, and the logical-to-physical register
permutation is `(6,2,0,4,3,7,8,5,1)`.

`--scope admissible` removes the six impossible guarded-case indices
`8202,8203,8204,8358,8359,8360`, leaving 8,385 cases. Those exclusions follow
from the independently checked product invariant initialized with logical
`T=W=H=0`; the other six logical registers are arbitrary natural numbers.
The full labeled source control-flow graph is checked before transporting the
invariant to a new layout. Both independently replayed blank starts, for
layouts 0 and 233, satisfy this root premise. This guard-only domain is still
broader than the invariant: **5,327 of its concrete register vectors violate
at least one other register's certified mask**. Its failed fixtures therefore
cannot by themselves exclude optimizations that exploit those masks.

`--scope product` is the recommended domain. It uses four concrete vectors for
each feasible guard, for 33,540 fixtures. Every one of the nine register values
respects the source site's certified mask, and the decremented register also
respects the selected guard. The four vectors choose minimum categories,
maximum categories, and two varied category assignments; category `>=2` is
represented by two or three. The construction is in
`../runtime/make_merge_cases.py`. It is still a finite sample of an infinite
product domain. The masks are an inductive overapproximation of source
reachability; a vector satisfying them need not occur on the actual blank run.

For all domains the target tape and head come from the attributed literal
register instruction contracts, not from the mutated machine. The runner first
replays the unmodified table on every supplied fixture. Every baseline replay
passes, and the fixtures exercise all 492 original state/read rows.

## Screening implementation and pruning

The simulator uses a 512-cell tape window with coordinates `[-64,447]` and
20,000 transitions of fuel for each fixture. It accepts a nonhalting instruction
only after a positive number of transitions, at the mapped dispatcher, with the
exact expected head and the complete expected tape. A halting fixture requires
an actual transition to the separate halt state 254. Merely reaching the
dispatcher does not finish an instruction.

An original trace that does not visit either fused state remains unchanged:
induction on the trace shows that each row and target used by the execution is
unchanged. This justifies skipping that fixture in the candidate replay. The
runner records all original row footprints, forms up to five probes per row
using seed 20261018, and then checks every affected fixture after the probes.
Thus probes only change rejection order, not the family or its final gate.
A timeout or a departure from the tape window is a failed finite gate; it is
not asserted to prove semantic inequivalence.

The executed sources for all three domains are retained in `legacy/`, with
their SHA-256 bindings in the result records. The portable runner adds input
validation and a standard-input transport mode to the same search algorithm.
Historical all/guard-only results came from the same algorithm with the guard
indices filtered internally in the latter. The portable fixture generator
emits already-filtered input. All 18 regenerated corpus hashes agree with the
research fixtures; the manifest and compact search summaries are retained in
`../../verification/fusion/`.

## Reproduction

Only Python 3 and a C++17 compiler are needed. Run from the archive root:

```sh
python3 code/fusion/run_family.py --layout baseline --scope product --output /tmp/fusion-baseline-product
python3 code/fusion/run_family.py --layout 0 --scope product --output /tmp/fusion-layout0-product
```

Replace the layout by `233`, `235`, `236`, or `237` as desired. Use `--scope all`
or `--scope admissible` to reproduce the older two fixture domains. Each run
regenerates one corpus, checks source-invariant transport when applicable,
compiles the C++ runner, streams the corpus through standard input, and writes `replay.json`, `search.log`, and the raw
summary in the requested output directory. The original six product runs took
roughly 47--53 seconds per layout on this environment; timings are not part of
the claim. No generated fixture bulk or binary executable is included in the
archive. Do not run Python with `-O`, which disables source-checker assertions.

To generate a corpus without running a search:

```sh
python3 code/fusion/make_cases.py --layout 0 --scope product --output /tmp/layout0-product.txt
```

## Optional broader, incomplete study

`general_row_search.cpp` drops the common-row requirement. It chooses one row
from either original state and synthesizes the other row freely. A lazy probe
can reject an entire such family when a fixture fails before reading the free
row. This separate layout0 study used the unrestricted 8,391-case domain and a
300-second bound, checked between state pairs. It completed only 908 pairs,
considering 3,616 fixed-row families: 1,921 were rejected before consulting the
free row, and 1,695 were concretely enumerated. It screened 1,667,880 recipes
with no survivor. **This search is incomplete**, and it was not rerun on the
product domain. Its raw result is `general-partial.json`; it does not support
an exhaustive statement about the broader family.

```sh
python3 code/fusion/make_cases.py --layout 0 --scope all --output /tmp/layout0-all.txt
c++ -O3 -std=c++17 code/fusion/general_row_search.cpp -o /tmp/general-row-search
cd /tmp
./general-row-search /tmp/layout0-all.txt 300
```

## Attribution

The baseline machine, instruction contracts, compiler machinery, and original
fusion-runner structure come from the supplied ProveIt research lineage and
its incoming `zfc-beyond246-research-20261018` packet. Attribution to Mira-Cult,
Jeff (`jeff87654`), Andrew James Wade, mira-emmy, and the ProveIt contributors
is retained in `../../reference/context246/NOTICE.txt` and the upstream notices
there. No replacement license is imposed on their material.

This contribution adds the exhaustive synthesized-other-row family, its
application to the five 246-state decoder layouts, the three-domain comparison,
and a portable reproduction driver. The product invariant and six guard
exclusions are prior research results; their independent rechecking and
transport are provided by the accompanying proof/runtime modules. Layout0's
underlying reassociation is also prior art; its use with this 246-state runtime
and these fusion searches is the scope of this experiment.

## Source specialization study

The `zero_specialization/` subdirectory contains three independently certified
source programs that erase two transfer loops proved empty by the product
invariant. Their emitted costs are 253, 247, and 254 states, so they do not
improve the 246-state record. Its README gives the exact scope, the 718 closed
layout proposals and 333 control-aware proposals, and independent replay commands.
