# Claim ledger

## Proved in this article

1. Static cancellation closure on usable pair columns is exactly directed reachability from anchors and initially deleted rows.
2. A dual tree succeeds on those matrices exactly when it hits every unanchored source SCC; existence is a graphic/partition independent-transversal problem.
3. The minimum number of additional arbitrary row deletions after the best tree equals the maximum color-set graphic rank deficiency. An optimal tree, seeds, schedule, and lower-bound packet are produced.
4. For arbitrary matrices, exceptional-row orderings and shared-witness partitions yield an exact `poly(input_bits) * b! * Bell(b)` algorithm, with at most `m(b+1)` clones per branch.
5. Abstract local selection is NP-complete even for entries in `{0,1,2}`, support at most three, and rooted-star dual graphs with paired arms and root loops. The reduction does NOT prove geometric realizability.
6. A conditional full-work budget specifies sufficient local and global bounds for `n^{O(log n)}`. Its hypotheses are not claimed to hold for all knots.

## Inherited and explicitly credited

The full-positive-cancellation / unit-column-peeling equivalence and stopping-set persistence are maintained ProveIt results. The source-authenticated two/three dual-tree cancellation interface is maintained ProveIt work. Independent representatives, graphical matroids, and the shortest-augmentation method are classical. The article includes a specialized proof and verifier design, not a claim to have invented those foundations.

## Executed

54 unit tests; 35,684 exact matrix/graph selection comparisons; all positive and negative packets replayed in that audit; 1,000 independent-transversal assignment comparisons; 500 optimum-deficit comparisons; 22,830 seed-set closure comparisons; 19,683 inherited peeling/positive-fill comparisons; 400 synthetic CNF formulas with 7,988 assignments; 40 further CNF/FPT comparisons; paired structural-family matrix benchmarks with raw timings and identical-algorithm controls.

The five-row loop example was reconstructed from maintained source text. The solver chooses row 1 and produces a valid four-pivot source-timestamp schedule. This was not a rerun of its original triangulation factory.

## Not executed / not established

No full native recognizer run, Regina run, native `propose_geometry` call, native complete test suite, production installation, or difficult-knot speedup is claimed. The native adapter's record translation alone was executed. No Lean or other proof-assistant verification was performed. No external referee review was obtained. The two named incoming dual-forest ZIP bodies were not audited, so exhaustive repository-wide novelty is not claimed. No geometric realization of the hardness gadgets is given. No general quasi-polynomial recognizer is established by this package.

## Safe interpretation of negative answers

`no` means that no dual spanning tree followed by the specified full positive cancellation completes the supplied fixed unsigned matrix. It does not mean non-handlebody, nontrivial knot, failure of another primal forest, or failure of the complete recognizer. `unknown` means the requested branch budget stopped the local search.
