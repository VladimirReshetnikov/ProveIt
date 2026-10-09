# Logical audit of the exact-search programs

## Scope and conclusion

The audited programs are the unmodified snapshots identified in `source_manifest.json`: `rainbow_exact_v5.cpp`, `rainbow_top_edges.cpp`, and `rainbow_edge_prefix.cpp`. The supplied v5 hash agrees with

`d3c14a9fb6e6b1b67f0060ae67244370aacd4ae905cb33dd84fa62808840541d`.

No logical bug affecting soundness or completeness was found in the declared range `1 <= n <= 10` and the target sizes used in the report. The later top-six-prefix variant changes only the accepted mode-name list; its recursion is the same algorithm audited below.

The large side-seven impossibility run was not independently rerun as part of this bounded audit. Its claim depends on the complete case records in the main package as well as the source correctness reviewed here.

## 1. State invariant and direct validity

At a recursive state:

1. `chosen` is a set of distinct points with all squared distances different.
2. `used` is exactly the set of its squared distances.
3. Every retained candidate has one radial distance to each selected point; these radial distances are distinct and avoid `used`.
4. Future edges must obey the current maximum allowed length.

The initial candidate lists in the single-anchor, diameter, and edge-prefix modes satisfy this invariant. All mask arrays have in-class zero initializers, so locally declared masks and candidate radial masks begin empty.

For a branch choosing candidate `v`, its radial set is added to `used`. Every retained `w` was compatible with `v`: their radial sets are disjoint, and the new edge color avoids both radial sets and `used`. Appending that edge color to `w`'s radial set therefore preserves the invariant.

The `need == 1` shortcut is sound because every candidate individually extends the selected set. The `need == 0` shortcut returns the already valid selected set.

## 2. Compatibility graph

The compatibility conditions are necessary and sufficient for the existing selected set together with two particular candidates to be valid under the current length cap. Every valid larger completion is consequently a clique in this graph.

The graph does not itself enforce inequalities between two different future-to-future edges. This is harmless: it is used only for necessary conditions, and subsequent recursive updates enforce the full distinct-distance invariant.

## 3. Palette, parity, and occupancy pruning

The radial union must contain at least `|chosen| * need` colors, because all selected-to-future edges of a completion must be different. The larger available-color union contains all colors of any possible completion, so its cardinality must be at least `target*(target-1)/2`.

Checkerboard parity counts precisely the odd-distance edges. The loop over additions to the two parity classes retains every possible final split.

The eight coordinate-parity classes determine squared-distance residues modulo four by Hamming distance. `generate_occupancies` enumerates every weak composition of the target size into these classes. Its requirements are the exact numbers of edges in the four residue classes. Filtering by current color capacities and by selected/candidate class counts is necessary for any completion.

Passing a previously filtered occupancy list to a child is safe: every child completion is also a completion of its parent. Word offsets in the masks are multiples of64, so the alternating parity and modulo-four bit patterns have the correct residue alignment in every word.

## 4. Greedy coloring and ordered branching

Each color class constructed by the greedy routine is an independent set: after selecting a vertex of that class, all its neighbors are excluded from that class's available mask. The routine removes every vertex exactly once, so the result is a proper coloring.

The recorded colors are nondecreasing along the resulting order. When branching in reverse order, the active vertices are exactly the unprocessed prefix. Its clique number is bounded by the current prefix color bound. Thus returning when that bound is less than `need` cannot discard a completion.

For a valid completion, consider its last vertex in this order. The corresponding branch includes it and all its earlier neighbors; subsequent branches exclude it. This partitions all completions and proves exhaustive coverage.

The top-edge variants additionally remove vertices of degree less than `need-1`, iterating that removal. Such a vertex cannot belong to a clique of size `need`. Dead vertices remain in adjacency storage but are excluded from the active and coloring masks; this only leaves harmless extra bits outside the relevant masks.

## 5. Unique diameter and its cube orbit

If a target configuration has `K=binom(target,2)` distinct squared distances, its largest is at least the Kth smallest member of the entire cube palette. The program enumerates every unordered grid edge meeting that threshold and keeps its lexicographically smallest image under the 48 cube isometries.

Every target set has a unique longest edge and can be carried into exactly one such edge orbit. Every other selected point has two distinct distances to its endpoints, both strictly shorter than the diameter, so it is in the initial candidate pool.

The recursive code sometimes writes `d <= max_distance`. At a diameter or processed-prefix state, that cap value is already in `used`, so the separate `!used.has(d)` check makes the effective inequality strict for every new edge.

## 6. Stabilizer reduction of the first remaining point

Let H be the complete setwise stabilizer of the anchored diameter. Its action preserves the initial candidate pool: distance-to-endpoint conditions are unchanged when the two endpoints are swapped.

For a valid set B of remaining selected points, choose the smallest integer point identifier among all images `h(v)`, with `v in B` and `h in H`, and call it r. Apply an element attaining r to the whole configuration. Then:

- r is the least point in its H-orbit;
- every other remaining selected point has identifier greater than r;
- the least image of every other selected point's H-orbit is at least r.

These are exactly the filters `rep[r] == r`, `s > r`, and `rep[s] >= r`. Hence some isometric representative of every completion survives. Skipping this reduction for small stabilizers in v5 loses speed, not completeness.

## 7. Unique second-largest edge

After fixing the unique diameter, the second-largest squared distance is at least the `(K-1)`st cube-palette value and is strictly smaller than the diameter. Its endpoints lie in the pool consisting of the selected diameter endpoints and the initial candidates.

All unordered pairs of that pool are considered, including pairs sharing one endpoint with the diameter and disjoint pairs. Canonicalization uses only the diameter stabilizer, under which this pool is invariant. Rebuilding the selected edge colors rejects every repeated length and every additional selected edge longer than the proposed second-largest one.

The new candidate pool contains every point of any completion with that second-largest edge. Setting the future cap to its length is therefore complete.

## 8. Induction for the longer edge prefix

At a prefix state, `processed` contains the distinct lengths of the already fixed largest edges. `selected` contains all their endpoints; `used` contains every pairwise length among those selected points, including some shorter lengths not yet processed. `previous` is the last processed length.

If r is the next rank from the top, its length is at least the `(K-r+1)`st palette value. It is also at least the largest unprocessed length already present among selected points. The code takes exactly these two necessary lower bounds.

The next edge's endpoints must lie in `selected` or the current candidates. Every such pair in the permitted length interval is enumerated. Active symmetries fix each previously processed unordered edge setwise. They therefore preserve the selected point set and the current candidate pool. Taking only the least edge image under this subgroup preserves one representative of every possible completion.

After adding the proposed endpoints, the program reconstructs all selected distances. It rejects duplicates and rejects any length larger than the proposed next length unless that length is already processed. Candidate radial sets are then rebuilt under the new cap. Each test is necessary for the proposed prefix, and every valid completion survives its own next edge choice.

The next active subgroup additionally fixes the newly processed edge. This preserves the induction invariant. The base call to the ordinary recursive search completes the proof.

If the selected set already has the target size, returning it is valid even when fewer than the requested prefix edges have been processed: the goal is to find a valid point set, and all its pairwise distances have already been checked. There is no negative palette index in the tested or later top-six modes; before the target number of points is reached, the number of processed edges is strictly less than the total target edge count.

The mutable global `max_distance` is set when ordinary search begins. The outer prefix recursion uses its own `previous` argument, so a failed deeper call cannot impose its smaller cap on a later sibling prefix.

## 9. Timeout and storage considerations

When an internal timeout is detected, the flag propagates to the top-level output and produces `UNKNOWN`, never `UNSAT`. Some setup loops check time less frequently, which can exceed a requested wall-time budget but cannot turn incomplete search into an impossibility claim.

For `n <= 10`, there are at most 1000 points and the largest squared distance is 243. The 16-word vertex bitset and four-word distance mask are sufficient. All indices and arithmetic quantities in the reported target sizes are within their declared ranges.

## 10. Bounded regression evidence

The reference harness compared each recursive search with a direct subset enumerator on 500 generated induced instances. All 1500 comparisons agreed, including 549 UNSAT outcomes. The seed and generator are shipped in the bundle.

The four diameter/prefix modes agreed on all 64 separately run small-grid diameter cases, for 256 executions. All SAT witnesses were independently verified by integer squared distances. The complete small-case outcome records are in `recorded/`.

These checks specifically exercise recursion, coloring, parity occupancy, core pruning, stabilizer restrictions, and the added edge-prefix logic. Their role is to support the manual audit; they are not a substitute for a complete record covering every case of a larger claimed impossibility computation.

## 11. Focused review of the complete side-eight run

After the top-six run completed, its frozen source was confirmed byte-identical to the reviewed top-six snapshot. The separate audit in `N8_RELEASE_AUDIT.md` and `audit_n8_release.py` checks all release manifest hashes, independently enumerates the required diameter orbits, verifies agreement of every case record with that enumeration and the final summary, and independently validates the twelve-point witness.

That check found all 23 required diameter cases, corresponding to 660 eligible unordered edges, with every case recorded as UNSAT. The resulting computational claim is a_8=12. The focused check did not rerun the full impossibility search and does not represent its execution logs as formal proof certificates.
