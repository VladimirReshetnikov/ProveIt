# Independent review: recorded nonproject input frontier

The reviewed source, README, pins and receipt are in `research/adaptive87-peer-nonproject-frontier/`. This separate checker independently reconstructs the selected producer rows and direct nonproject edge multiset from the pinned predecessor receipts and producer metadata. It also re-observes every reported producer path and all three mirror comparisons. It found no concrete discrepancy in the scoped claims.

The reconstructed trace has 673 distinct selected producer rows; 130 of those rows have at least one selected direct nonproject input, producing 1,204 edges over 95 names. The names comprise the 94 Foundation/Mathlib/Lean names in the two previous lexical frontiers and the additional direct `Init` input. The same name has one recorded SHA-256 across these selected edges. Of the 68 currently unavailable producer-path edges, 38 paths are reconstructed from historical package mirrors and 30 are directly recorded; they cover 26 distinct Foundation names. All 26 corresponding alternate rebuild objects currently exist and have different bytes from their recorded hashes. Every currently present recorded or reconstructed producer path matches its recorded hash. The existing Lean binary matches the two pinned recorded binary hashes.

This is a point-in-time check of paths and hashes, not a claim that the missing objects were absent during their historical builds. Inferred mirror paths are not historical recorded paths. Different hashes do not prove incompatibility, and agreement on direct hashes does not authenticate package-transitive or dynamic dependencies, companion files, a current project source closure, or a coherent future `LEAN_PATH`. The two preceding frontier receipts are pinned, not independently rebuilt here. The alternate Foundation manifest is an identity observation, not evidence tying its transitive providers to the historical objects. No Lean build or staging was performed.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B reviews/adaptive87-peer-nonproject-frontier-second-independent/check.py > /tmp/adaptive87-peer-nonproject-independent-current.json
cmp reviews/adaptive87-peer-nonproject-frontier-second-independent/receipt.json /tmp/adaptive87-peer-nonproject-independent-current.json
```

The check reads ephemeral `/tmp` evidence, so later changes or removals can invalidate the point-in-time receipt. The review does not modify any producer or historical packet.
