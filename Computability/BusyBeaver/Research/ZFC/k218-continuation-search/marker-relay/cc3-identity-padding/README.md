# Neutral source padding around the CD6/CC2 route

Two all-natural source replacements remove all nine occurrences of
`P = (CD6,CC2)` from the primary K218 source. Each costs **207 distinct
subtrees and 4,762 leaves**, compared with the accepted source's 205 and
4,744. Neither replacement has yielded a candidate table: all 38 allocation
attempts stop at missing generic primitive entries.

For each register r=0,…,8, let `N_r=(CI_r,CD_r)`. The two replacements are

```
P_left  = (N_r,(CD6,CC3))
P_right = (CD6,(N_r,CC3)).
```

The [ordinary proof](proof.md) preserves the entire register vector and
the exact open return behavior. The source readers also check every retained
primitive effect and successor after contracting the added neutral pairs.
The second placement independently compares two complete CFG resolvers.
Both families retain depth38 and maximum zero-run6. These transformations
change the primitive word; the preceding [retag obstruction](../retag-obstruction/README.md)
concerns reassociation with unchanged ordinal control flow.

| Source option | Variants | DAG / leaves | Allocation result on each backend |
| --- | ---: | ---: | --- |
| Identity before CD6 | 9 | 207 / 4,762 | All rejected |
| Identity after positive CD6 | 9 | 207 / 4,762 | All rejected |
| Swap registers5/6 in all four complete equality macros | 1 | 206 / 4,744 | Rejected |

The swap uses the previously proved symmetric clean equality contract. It
removes the eight late CD6/CC2 occurrences but leaves the initial occurrence.
The prior all-natural affine recognizer finds35 inherited blocks and **no
identity transformer**. This is a census of that proved recognizer, not a
claim that every possible total identity block has been classified.

## Allocation evidence

Root's context-aware allocator was adapted only to accept an explicit input
table and require exact action-table identity on the unchanged source.
Both controls pass: accepted primary218 and the known-invalid relay217
retain all their original actions and state counts. Identity preservation
does not repair the relay's existing primitive-runtime failure.

For either placement, r≠6 needs a generic right-CD_r entry that the allocator
does not provide. At r=6, it gets further but lacks generic right-CC3.
The comparator swap lacks right-CD5. No guessed entry is supplied. These
are interface rejections, not measured state costs or impossibility proofs.
The two controls and38 variants took less than seven seconds in total.

The [first source results](evidence/result.json),
[second source results](evidence/v2/result.json),
[identity controls](evidence/allocator/identity-results.json), and
[complete allocation records](evidence/allocator/results.json) retain the
actual inputs, generated sources, rejection details and process stdout/stderr.
The first source writer's own syntax typo and exact correction remain in
[history](evidence/history/own-draft1/failure.json). Source measurement tool
chunks are described in [publication.json](publication.json); they are not
represented as separately captured raw shell logs.

## Reproduction and scope

From the repository root, with fresh output directories:

```sh
P=Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/cc3-identity-padding
python3 -B "$P/code/measure.py" --repo "$PWD" --output /tmp/cc3-first-new
python3 -B "$P/code/measure_v2.py" --repo "$PWD" --output /tmp/cc3-second-new
python3 -B "$P/code/context_allocate.py" --repo "$PWD" \
  --table Computability/BusyBeaver/Research/ZFC/candidate-k218/k218.native.tm \
  --source /tmp/cc3-second-new/post-test-pad-r6.sites.json \
  --output /tmp/cc3-allocation-new
```

Use the marker-relay `relay217.native.tm` for the second backend. Run the
same command on `candidate-k218/sites218.json` first to exercise the required
identity control. The source drivers' portable variants change only path
and argument setup; their diffs and executed originals are retained. No
new Lean/Rocq proof, startup, primitive-runtime check, calibrated smaller
machine, or optimality claim accompanies this packet.

`review_upstream_reflection` authored the source experiments and ordinary
proof. The allocator is root's earlier context-aware implementation;
`opening_encoder` identified that current implementation. No independent
peer review of these new neutral-padding proofs is claimed here.
