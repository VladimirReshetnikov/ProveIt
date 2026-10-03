# Independent review: complete U15 loader offset 506

**PASS, with one documentation correction applied.** The frozen source removes exactly one paid addition from each of six ordinary-input schedules. Both raw schedules are unchanged. Every complete polynomial, comparison residual, supplied coordinate, semantic domain and inherited exact degree is preserved. No theorem or source-code defect was found.

Reviewed source: `u15_packed_loader_offset506.py`, SHA256 `b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a`. The direct parent is `u15_packed_cross_projection507.py`, SHA256 `dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4`; the independent checker also authenticates its frozen complete receipt, SHA256 `9d4cdfb040c756c3d7f11b15cf0a9ad42b8e7dd2571053fa1f5cc1196723332b`. It reads the actual parent packets from that receipt rather than trusting the candidate's reported counts or proof results.

## Mathematical and source audit

I read the complete candidate source, its complete direct-parent source and the companion proof note. In every ordinary form the actual old source contains

    Ahat = u+1
    scaled_Z = 16*Ahat
    F3 = scaled_Z-8

and the new source contains

    scaled_Z = 16*u
    F3 = scaled_Z+8.

An independent exact polynomial expansion gives `F3=16u+8` for both. The removed `input__restored_Ahat` register has exactly one actual complete-source consumer, `input__and__scaled_Z`, which itself has exactly one consumer, `input__and__F3`. These are arithmetic registers, not supplied coordinates. The complete DAG contains no other use requiring the deleted addition to be recomputed.

The checker proves this local identity first, then uses an independent shared expression interner to compare the entire old/new source with the equal `F3` value treated as a proved substitution. It checks that the atom `u` is itself unchanged. Every common emitted register is then exactly identical except the explicitly changed `scaled_Z`; every comparison operand, native factor and complete output is identical. All finalizer rows remain literal and every gate is live. This is an all-value polynomial proof, not a zero-only argument, a hash-based equivalence assumption or a random test.

The active loader-restoration map contains fourteen emitted definitions. The removed historical fifteenth field has the explicit mathematical formula `input__Ahat=u+1` in a separate proof-only field. That formula is not represented as an unpaid live source register. All current arithmetic exports are available and denote the same values as before. The positive restoration claim for the old ancestor field is unchanged because its mathematical value is unchanged.

Complete source equality imports the exact degree of each parent polynomial immediately, with the same fixed-program uniformity. I verified all eight nested parent degree certificates against the frozen parent receipt and independently recomputed every new syntactic degree upper bound. I did not infer exact degree from those upper bounds or rerun a redundant leading-coefficient computation. The existing parent proof and this full polynomial identity together establish the degree transfer.

| Form | New M | New A | Complete operations | Witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Raw ungrouped |116|205|321|51|11|1936|
| Raw grouped |116|203|319|51|10|3464|
| Ordinary ungrouped |209|309|518|87|31|1936|
| Ordinary grouped |209|297|506|87|25|4881|
| Frontier 0 |209|297|506|87|25|4881|
| Frontier 1 |209|299|508|87|26|3120|
| Frontier 2 |209|301|510|87|27|2116|
| Frontier 3 |209|303|512|87|28|1936|

I independently recounted both the certificate prefix and the full polynomial schedules. Each ordinary source saves exactly one addition and no multiplication. All integer/rational zero relations follow from identical full polynomials, without a new sign condition. The public semantic domains remain positive integers, except that the two raw tape inputs may be natural zero. Valid fixed program slices and unbounded-duration first-halt semantics remain inherited hypotheses. This review does not materialize a complete universal Pell witness, revisit all 4,140 partition forms, or claim a change to the separate 87-operation universal equation.

## Guard and replay evidence

The independent checker authenticates the candidate source before executing it, checks the pinned direct parent and saved parent receipt, then audits all eight actual builds. Its bounded suite passed:

- Eight exact full source/output identities, six independent local expansions and 183 exact residual identities.
- Eight exact-degree certificate transfers and complete independent live-gate ledgers.
- Eighty complete integer evaluations, including 48 signed cases, and 16 rational evaluations.
- 360 malformed-call rejections, including coefficient-type substitutions at 200-digit inputs and wrong coordinate/packet shapes.
- 24 nested defensive-copy checks, two warm source-pin tests on private copies of the direct and inherited parents, and optimized-execution rejection.

The source pins are checked through warm cached calls; direct-parent bytes are executed with `compile` rather than the new wrapper loading cached bytecode. The review does not claim protection against arbitrary Python monkeypatching or audit every historical import mechanism afresh. The source and ancestor cache holders remain private; public packet and source accessors return independent copies.

One initial companion-note statement incorrectly claimed that replay needed no third-party arithmetic library. A plain-interpreter attempt demonstrated the historical `centered_states611.py` import of SymPy. The author corrected that claim; I added the explicit research-environment command at the root reviewer's request. This was documentation only: the frozen source and author receipt did not change.

Portable independent replay requires Python with SymPy available through the historical dependency chain:

    /path/to/research-venv/bin/python review_u15_loader_offset506.py \
      --source /path/to/u15_packed_loader_offset506.py \
      --root /path/to/native-stream-queue \
      --output /path/to/fresh-review.json \
      --expect /path/to/review_u15_loader_offset506.json

The helper and receipt contain no absolute worktree paths. Source authentication occurs before import; tests modify only temporary private source copies. The fresh replay reproduced the full independent receipt.

Root separately replayed both the author suite and this independent checker in the research environment. Both saved receipts matched; the independent replay was byte-identical.
