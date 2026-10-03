# Independent review of the mixed per-step branch search

PASS for the frozen search source `ad761700350ea15ba048248ede5553f09eb407e9fc9d7bc0078b8c8c61bca625` and receipt `dda2113548c9811336b9a601841b0dfeb6050d53554ae0e6f157a91a138551fd`. I read the entire search and companion note, reconstructed the finite enumeration independently, regenerated and recounted all 744 literal schedules, and checked the four complete winning polynomials with the already frozen independent composition auditor. No source or receipt change requested.

The search correctly enumerates `(omitted branch)^h` independently at each step, crossed with three guard schedules and four endpoint modes. The actual two-step fixtures have B=2 and h=2, giving four layouts and48 schedules each; the three-increment fixtures have B=3 and h=3, giving27 layouts and324 schedules each. The total is62 layouts and744 schedules. My checker compares the complete ordered list of keys and ledgers, so it verifies multiplicity and coverage, not merely the total length.

Constant-index lists form a literal subset of that same search, with the same four endpoint modes and cost metric. There are24 such schedules per two-branch fixture and36 per three-branch fixture. The code minimizes the pair `(total operations,multiplications)` and keeps the earliest enumerated tie, which agrees with the stated tie convention. It does not mistake the last visited candidate for the winner, prune any unsampled layout, or claim completeness over arbitrary arithmetic circuits. Including the no-endpoint option in both comparison families makes the baseline fair.

I regenerated the four exporter certificates through the pinned original producers, compared their complete saved descriptors, and independently recounted every emitted binary operation, checking fresh source names, exact literals, topological closure and liveness. All63,388 charged nodes are live. Nonunit constants, affine rows, endpoint-mask arithmetic, all squaring and final sums remain paid by the unchanged emitter. The full saved winning packet equals the freshly emitted packet, not just its ledger.

| Fixed source | Constant-index minimum | Full per-step minimum | Omitted branches | Mode / endpoints | Witnesses |
|---|---:|---:|---|---|---:|
| INC2;DEC2, h=2, native y,T |46|16M+28A=44|[0,1]|Horner / both|6|
| INC2;DEC2, h=2, compact-clean T |45|17M+26A=43|[0,1]|Horner / both|6|
| Three INC2, h=3, native y,T |86|26M+60A=86|[1,1,1]|Factored / both|15|
| Three INC2, h=3, compact-clean T |83|26M+57A=83|[1,1,1]|Factored / both|15|

The existing zero-fiber proof permits different omitted indices at different steps: each step's nonnegative grouped penalty independently restores its missing selector, and all rows use that same affine restoration. The choice `[0,1]` is fixed compiler data; it does not add a premise that those branches execute or omit tests on other supplied tuples. The complete polynomial auditor independently expands every original certificate constraint and endpoint mask for each winner and proves its full displayed correction to the projected parent. All four winners have exact degree three and the declared witness lists. Sixteen complete original natural witnesses project and restore exactly, with zero complete polynomial on both sides and the original offsets recovered. These examples supplement the already reviewed general theorem.

This review explicitly reuses the frozen independent coefficient engine (`review_three_mass_projected_endpoint_penalties.py`, hash `a348f9ffa8e411892cd892986b304bec291adbeb500b167e267632b0327d6be9`) for the four winners. It does not claim a second algebra implementation or repeat the larger783-form composition audit. The new finite-grid construction, tie/minimum calculation and all744 gate recounts are independent of the search helper's `run`. All six dependencies, search source, author receipt and original archives are pinned before use; source bytes are compiled directly instead of trusting cached bytecode. Receipt comparison is type-sensitive. Fresh replay passed.

A wording clarification is resolved in the final author's note (SHA256 `ccf86f4b1a03a7a7454ec097159a45d85f7f9e5126808f37d14d387558eb3b83`). The winning mode changes from initial-only to both endpoint penalties, so the note now states precisely that no new emitter rewrite is introduced and every original source condition, endpoint and domain requirement remains enforced; the selected endpoint mode may differ from the uniform baseline. This affects no circuit, theorem, count or receipt.

No claim follows about arbitrary-program optimum, fixed-arity unbounded computation, an ordinary-counter decoder, or the global87-operation bound. The source table and horizon remain external and the raw-x fixed-name prototype interface is inherited. The comparison to the separate quadratic endpoint-only variant correctly retains the degree and witness tradeoff.

The portable independent checker uses explicit paths and produces `/tmp` output only:

```sh
python review_three_mass_mixed_branch_search.py \
  --source three_mass_mixed_branch_search.py \
  --receipt three_mass_mixed_branch_search.json \
  --root /path/to/native-stream-queue --repo /path/to/Proofs \
  --output /tmp/mixed-branch-review.json \
  --expect review_three_mass_mixed_branch_search.json
```

Independent totals are62 complete layouts,744 fresh literal schedule recounts,63,388 live paid gates, four entire winning polynomial identities and16 complete natural lifts. No original suite, repository edit or Git mutation was performed.
