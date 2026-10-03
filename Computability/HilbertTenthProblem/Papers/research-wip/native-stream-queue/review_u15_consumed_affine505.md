# Independent review of the complete U15 consumed-affine505 rewrite

**PASS; no correction requested.** The exact complete polynomial is preserved
on the same supplied coordinates in each of the eight published forms. The
ordinary frontier is now **505/4881, 507/3120, 509/2116, 511/1936**
(operations/exact degree), with 209 multiplications and 87 positive witnesses
throughout. Every form saves exactly one paid addition relative to 506.
This is an improvement to the complete U15 route, not to the separate universal
87-operation circuit.

Reviewed source SHA256:
`a8716b7ca82f703944993a247da89fa2a9a70ccfb5db11521161014edc4a3533`.
Its saved receipt is
`6376193a420efc81cffbd7becd51d7b2f84d4d44fa3706e5996e06920e06bca5`.
The complete companion note was read, including the optional search-helper
qualification; that note revision is
`392565d45b58dc7e556aaa8847a6b278dff6e7d202c5e844ad3de77fcb15477d`.
The implementation and receipt stayed frozen during this review. The later
editorial addition reporting binary seeds 500 through 3499 (nine further
90-gate schedules, none below 90) correctly limits the observation to that
finite search. Its separate search receipt and reproduction commands are
outside this independent arithmetic review; no optimality result is implied.

## Independent algebra and whole-source accounting

The checker authenticates the original 653 source
(`ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318`)
and extracts its literal `TABLE` through Python's syntax tree without executing
that file. It independently parses the 29 transitions, applies the recorded B/J
state permutation, and derives the nine target coefficient vectors in all 29
independent shifted selectors and the constant coordinate. It does not use the
candidate's sparse-polynomial or expression-signature proof routines.

Both actual emitted affine closures have exactly those vectors. In particular,
the read and direction offsets are 14 and 15, the two write parts have offsets
9 and 8, and the centered source/target coefficient sums are 6 and −17.
Consequently `Qdev+7` has constant 1 and `Ndev` has constant 17 after shifting
all selectors. The double-write ports cost their actual multiplication gates;
the two intermediate write ports remain emitted. The old closure has 91 gates
(6M+85A), and the new closure has 90 (6M+84A).

After independently proving these nine affine identities, a separate exact
expression interner compares the complete sources beyond the nine cuts. All
183 comparison residuals across the eight forms, all 37 emitted native factors,
every active semantic/tag/loader export and each complete polynomial output
agree. No other private affine register escapes the replaced closure. The
retained source rows and finalizer tails are literally unchanged in order.
The supplied parameters, witnesses, valid fixed-program interface, comparisons,
unit grouping and ancestor relation metadata agree with the authenticated 506
receipt. The latter receipt is pinned separately at
`8337d0ec9ddf7d5857e1d64bf33798e7ae149494346855120e7c8346b129800e`;
its compiler source is pinned at
`b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a`.

The checker independently traces every paid gate back from the output: all
3,692 gates across the eight sources are live. It recounts all operations,
including constants and finalizers, and recomputes the syntactic degree bound.
For anchor finalizers it separately evaluates
`U*(1 + sum retained_residual^2) - 1`; for the other forms it evaluates the
complete sum of squared comparison residuals. These match the emitted source.

| Complete form | M | A | Total | Witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Raw ungrouped |116|204|320|51|11|1936|
| Raw grouped |116|202|318|51|10|3464|
| Ordinary ungrouped |209|308|517|87|31|1936|
| Ordinary grouped |209|296|505|87|25|4881|
| Frontier 0 |209|296|505|87|25|4881|
| Frontier 1 |209|298|507|87|26|3120|
| Frontier 2 |209|300|509|87|27|2116|
| Frontier 3 |209|302|511|87|28|1936|

Exact degrees transfer through the proved complete polynomial identity; the
parent's exact-degree certificate is copied intact under the new certificate.
This review does not substitute a finite evaluation for that degree argument,
or repeat the ancestral leading-coefficient calculation. The same identity is
uniform in the fixed parameters, so the inherited fixed-program qualifications
remain necessary and sufficient exactly as before.

## Domains, metadata and executable boundary

The rewrite is an all-value polynomial identity over integers and rationals,
stronger than equality only at positive zeros. It uses no Boolean, native norm,
Pell, or zero-residual assumption. Hence every protected norm sign and the sole
unprotected checksum retain their previous obligations, without a new sign or
witness argument. Ordinary input, first-halt behavior and unbounded duration
transfer unchanged. Raw half tapes retain their natural-domain exception to the
otherwise positive supplied coordinates. No external horizon or input decoding
has been introduced.

Historical transform descriptions are archived intact under
`parent_transform_provenance`; current aliases all name live registers with
unchanged values. Current parent metadata names 506, and current ledgers describe
the actual new source. No stale 506 transformation is asserted as a description
of the new affine rows.

The independent executable suite passes 80 full integer evaluations (40 signed),
1,830 numeric comparison checks, 16 rational evaluations, 458 malformed-call
rejections, 32 nested defensive-copy checks, both raw zero-tape cases, two warm
source-pin mutations and optimized-mode rejection. It covers source coefficients
changed to floats/Booleans, list/tuple mutations, source/metadata corruption,
invalid flags/indexes, incomplete or extra assignments, and domain violations.
The full author default replay also matched its frozen receipt: 128 integer
identities, 16 rational identities and 488 rejection tests. These finite checks
supplement the exact coefficient and complete-DAG proof.

The cache holders are private. Every public canonical operation rechecks direct
and historical source pins, exact canonical descriptors are type-sensitive,
and source bytes are compiled directly for the immediate parent. Returned
builders, parent descriptors, polynomial rows and replacement rows do not expose
mutable cached state. Historical dependencies need SymPy; `-O` is deliberately
rejected because those dependencies use assertions.

## Reproduce and scope

From any working directory, with the reviewed compiler and JSON together:

```sh
/tmp/diophantine-research-venv/bin/python /tmp/review_u15_consumed_affine505.py \
  --source /tmp/u15_packed_consumed_affine505.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect /tmp/review_u15_consumed_affine505.json
```

Adjust paths after vendoring; the helper has no permanent `/tmp` dependency.
`--output` writes a new review receipt, while `--expect` compares exact JSON
types without modifying it. The review reads the complete new source and note
and authenticates the actual parent source/receipts. It does not re-prove the
ancestral U15 universality or construct a full Pell witness, rerun the 1,500
search seeds, claim a minimum affine circuit, or re-emit all unit partitions.
Only the eight concrete complete sources listed above are certified here.
