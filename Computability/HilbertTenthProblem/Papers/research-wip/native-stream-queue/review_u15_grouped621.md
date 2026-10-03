# Independent review of the 621-operation grouped U15 compiler

**PASS on the repaired frozen source; no unresolved finding.** The ordinary-input circuit costs 621 = 252M + 369A, and the raw-half-tape circuit costs 378 = 144M + 234A. Both compute exactly the same complete polynomial as their respective 646/403 parent, on every integer assignment. Consequently the supplied positive zero sets, ordinary input interface, witnesses and valid program slices are preserved without any witness change.

Reviewed source `u15_packed_grouped_projections621.py` has SHA256 `8cadeb24c695b1956cd5cb25f93d41261065ddc45c116d7c9b0d0e3d7e4906d3`; its receipt has SHA256 `07098dc298ed1dfe94c10ba93f495d7838ad5320edafb3fe0a3cb7d1485c3088`. The complete companion note was read, at SHA256 `ad26d1167239eb99def8738856f3b4a2c3e59c1d68e293a7cd72942f6735e5ff`. The comparison parent is frozen composed646 source `d2ec28b859b43e93396f66395866b3f18098a959da22c1a5559fc4c1be2cdeb7`. The compiler also checks the frozen baseline653, relabel652 and truth647 source pins before construction.

## Algebraic proof and arithmetic accounting

I independently expanded J, Q, S, N, Dir, W and WD into length-30 integer coefficient vectors: 29 edge-hat coefficients and their constant offset. In both raw and ordinary forms, the two emitted sources agree exactly with each other and with the literal relabeled table formulas. In particular, these checks retain the `edge_i - 1` offsets. All fourteen source-state pair sums are paid gates. Each participates in J and reaches the final output.

With only those seven proved affine identities treated as shared formal symbols, independent exact structural interning verifies all 57 comparison pairs across the two forms, all 62 named ordinary/semantic/tag/computed-truth register expressions, and both complete output expressions. This verification uses exact term keys rather than numerical evaluation or digest equality. All remaining operations are interpreted literally, apart from commutative operand ordering. It proves equality of every comparison residual and of the entire final polynomial over the integers; the same polynomial identity also holds over the reals.

I independently reconstructed each complete sum-of-squares finalizer from its comparison list, checked source closure and complete output liveness, and counted every binary operation. The cumulative addition savings at J, Q, S, N, Dir, W and WD are exactly `[0, 13, 13, 15, 19, 23, 25]`. Thus the initial fourteen pair additions do not create an unpaid precomputation: the J prefix has unchanged cost, and the later projections save exactly 25 additions in total. Multiplication counts do not change.

| Form | Certificate | Complete polynomial | Comparisons | Positive witnesses |
|---|---:|---:|---:|---:|
| Natural raw half tapes | 133M + 213A = 346 | 144M + 234A = 378 | 11 | 51 |
| Ordinary positive input | 206M + 278A = 484 | 252M + 369A = 621 | 46 | 102 |

Both propagated degree bounds remain 1936. Since the complete polynomials are identical, the separate reviewed exact-degree-1936 certificate for the parent immediately transfers. The new compiler correctly leaves its own propagated ledger labeled as an upper bound.

## Public guard and import review

The initial frozen source `8ae95be4502ed2fce6dd33af4d4baa47a3b367194f5478d5170b39ea66df6262` exposed the mutable canonical bundle through public `context(root)`. I reproduced a false accepted output by changing that bundle's final polynomial row to `(output, '-', 0, 0)`: subsequent `build`, `checked` and `evaluate` accepted the poisoned source and returned zero on the all-one tuple, whereas the parent returned a nonzero value.

The author repaired this by making the internal holder `_context`, with no public `context` alias. The documented public packet, parent and source accessors all return defensive copies, and my cold regression confirms the old public surface is absent. Direct mutation of conventionally private implementation objects is outside the public API contract, consistently with the parent compilers.

I tested exact integer and Boolean domains, including float and Boolean coefficients, rational coordinate objects equal to integers, missing/extra coordinates, malformed metadata/container types and a forged zero-output row. The two cold loader tests install either a no-file stub or a foreign-root stub before construction; the genuine complete packet is rebuilt and the caller's exact stub object is restored. Public calls recheck the selected pinned sources; optimized Python is explicitly rejected before inherited assertion-based constructors can run.

## Replays

The independent portable checker and receipt are `review_u15_grouped621.py` and `review_u15_grouped621.json`. It accepts explicit paths and has no permanent temporary-source dependency:

```sh
python review_u15_grouped621.py \
  --source u15_packed_grouped_projections621.py \
  --root /path/to/native-stream-queue \
  --output /tmp/review_u15_grouped621_replay.json
```

Independent checks passed: 14 exact affine projections; 57 residual-pair DAG identities; 62 semantic/tag/truth DAG identities; two exact complete outputs; two independent complete finalizer/ledger/degree/liveness audits; 14 projection-prefix cost checks; 28 paid pair gates across the two forms; 96 complete integer SOS evaluations, including 48 signed cases and 2,736 individual residual comparisons; eight rational polynomial evaluations; 1,421 malformed public calls rejected; six nested defensive-copy checks; and two cold import-isolation checks.

I also ran the author's default read-only receipt comparison from `/tmp`, with an explicit repository root. It passed with 128 full polynomial identities, 64 signed cases, 3,648 residual identities, 1,243 rejected malformed calls, six defensive-copy checks, two cold import checks, and the new unexposed-holder regression. The saved receipt hash remained unchanged.

This review establishes an exact source-sharing reduction. It does not materialize enormous native Pell witnesses, strengthen the inherited program-loader theorem, assert optimality of the grouping, or alter the established 87-operation universal bound.
