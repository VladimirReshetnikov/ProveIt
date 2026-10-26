# Final delivery metadata check

**Latest checked HEAD:** `45ac0dfc366f798d4686070a89d66e8dafdb6879`.

**Substantive exclusion review cutoff:** `7def5e00ef3593b296eb595add1d955d27121d0c`.

**Result: the same 22-packet exclusion corpus; no additional proposal.** The final HEAD check changes the packet's location, not the novelty decisions. The report can retain its substantive cutoff and cite this delivery check separately.

## What was verified

All twenty-one existing packet directories, `2026-10-26a` through `2026-10-26u`, have identical Git subtree IDs at both commits. Their contents are therefore unchanged.

The new directory `2026-10-26v` is the already audited `ProveIt_Lean_Simplification_Round3_2026-10-26.zip`. The comparison uses the saved archive bytes and Git blob IDs, without downloading another archive:

- 106 placed members match the archive byte-for-byte.
- The remaining placed member, `baseline_audit/ASSUMPTION_LEDGER.csv`, changes only CRLF line endings to LF. Normalizing the archive's line endings gives the placed bytes exactly, and parsed CSV records are identical.
- All 878 omitted members have Git blob IDs matching their archived bytes. `OMITTED.tsv` maps them to repository copies.
- The 107 placed members plus the 878 omitted members are disjoint and account for all 985 archive members.
- The only two additional files in v are `PLACEMENT.md` and `OMITTED.tsv`, which record placement and deduplication.

Packet v's subtree is `b8d8ffcdf304826603742c71137a14142cfe74dd`.

## Index and adoption changes

The research README adds v and updates the omission range from b–u to b–v. The incoming README updates the placed count from twenty-one to twenty-two and adds the Round3 placement link. The `docs/incoming` tree now contains only its README.

The ADOPTION diff updates references from retired ZIP paths to placed packet letters and records implementation/status corrections for previously excluded mechanisms: signed-root recovery, `nat_zero_or_succ`, pairing projections, native coefficient bounds, decoder invariants and high-color fibers. It introduces no additional proposal mechanism affecting this report.

The exact old/new metadata, all compared member names, the archive partition result, line-ending comparison, and the index/adoption diff are recorded in `DELIVERY_CHECK.json`.

## Consequence for the final report

The four retained directions remain vector-period normalization, the fixed-index Pell-six threshold, symbolic selector color moments, and canonical recognition of arbitrary allowed operating rows. Interval induction and shared-edge construction remain excluded. At delivery the same twenty-two packets are all placed, a–v; there is no pending incoming archive.

This is a read-only metadata and content-identity check. Source compilation remains tied to the original proof pin; the main review separately checks target-file identities at the delivery HEAD.
