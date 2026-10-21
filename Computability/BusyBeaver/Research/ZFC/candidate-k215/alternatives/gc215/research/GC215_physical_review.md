# Independent physical review of GC215

## Accepted literal machine

The final native table is `GEN_C215.native.tm`, SHA-256
`a5d8dfeb92a6ae843692c65b5eaf69b845b08b48d65dc011ba8a457e4faec67d`.
It has 215 working states, 430 rows, start control 0, and a separate halt
control 254. All 215 working states are reachable in the rooted transition
graph. The dense sorted-label version has working states 0 through 214,
halt control 215, dispatcher 81, and SHA-256
`ccabf998e346356edb33a829a8c2ab7a24b69f032349e9228f53e2295337ec0f`.

The exact parent is the corrected 216-state allocation with SHA-256
`f0b7ae5e41fb6445afd1bf5e1618f6dd059c1dacbce47d3f81086ef69da33629`.
The discarded earlier allocation did not protect the engine use of row
134/0 and is invalid. None of the accepted claims uses that table.

## Verified physical mechanism

The new fold identifies old state 310 with state 129. Its two origins have
opposite left-neighbor markers because their complete incoming censuses are
`312/0 = 0 R 310` and `211/1 = 1 R 129`. Their read-zero actions agree. The
new read-one action `129/1 = 1 L 216` branches through an existing chain,
taking three or five steps according to the preserved marker. These blocks
agree exactly with one old step in state, head, and tape, after the label
identification. Every other row commutes with that identification.

The standalone `check_decoder_merge.py` checks all table bytes, the exact
construction, the incoming census, the six helper rows, and all four finite
blocks. It produces the dense table and a checked bijection. The induction
is valid for every initial binary tape and head position from control 0.
It does not assert arbitrary-control equivalence with an unconstrained
marker at old state 310.

## Independent startup

`check_startup_independent.py` imports none of the compiler, symbolic runtime,
or primary bootstrap modules. It replays both native and dense tables in a
bounded bytearray with checked bounds and compares every saved transition.
At exactly 68,710 steps it obtains native dispatcher 84 (dense 81), head −2,
and exactly the entire prescribed 100-one-cell tape. The head range during
this finite computation is −12 through 226.

Its separate source interpreter resolves cuts by lexicographic prefix bounds.
It validates the source as a complete ordered prefix code and independently
matches all 177 saved AX-prefix records, beginning at ordinal 25 with logical
registers `[1,0,2,0,0,0,0,0,0]`. The endpoint is ordinal 58, address
`00110010010110010`, logical registers `[1,0,0,0,0,0,0,18,0]`. Reconstructing
the physical registers, 63 zero spare blocks, header, and address gives exactly
the finite binary endpoint.

This finite startup check is separate from the universal symbolic primitive
check. The latter was independently completed by the source agent on the
literal final table: 6,151 guarded primitive cases, all 430 rows covered,
1,617,679 symbolic rules, positive duration lower bound 5.

## Scoped novelty

The supplied `corpus128/` contains raw bytes for 128 distinct complete,
graph-reachable 215-state tables. `215-corpus.json` records their 399 paths
in the pinned repository and six pending ZIP archives. There are 86 rooted
graph families up to state relabeling and global reflection.

`check_novelty.py` validates every raw representative against its filename and
provenance, then attempts the forced rooted state bijection in both move
orientations. GC215 has no match. Each rejected comparison records a finite
write/direction or bijection conflict. This is a reproducible graph-novelty
claim relative to the supplied corpus, not a claim of semantic inequivalence
or a complete literature search.

## Further 214-state searches

The new GC215 radius-five arbitrary-tape window abstraction has 88,375 local
configurations, no absent state-symbol row, and 31 pairs distinguished by an
adjacent marker. The following bounded searches found no additional fold:

| Search | Limit | Attempts | Result |
|---|---:|---:|---|
| Both-branch positive joins | 48 TM steps | 19,835,232 branch candidates | No fold |
| One changed branch | 48 TM steps | 424,840 candidates | No fold |
| Two folds sharing a selector | 48 TM steps | 24,687 providers | No fold |
| Shared selector with positive old/new joins | 48 TM steps | 24,687 providers | No fold |

These are bounded search outcomes, not lower bounds on machine size.

A separate all-tape-equivalent experiment redirects `26/0` from state 134 to
194. The sole incoming row to 26 establishes a zero on its right, so the
old route `26 -> 134 -> 17` and the new route `26 -> 194 -> 17` agree in two
steps. This removes one engine constraint on half-row 134/0 and may assist a
future allocation, though its remaining decoder obligations still apply.
The same bounded two-branch search found no 214-state fold in that optional
variant; its one-branch search tried 426,560 candidates with no hit. The
variant is not the final GC215 table.
