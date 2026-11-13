# Independent historical AQ29 paired-artifact audit

This audit checks the observed terminal result and all 1,210 recorded peer
rows against the frozen historical parent snapshot, then independently
compares every sibling row and normalized output-companion record. It builds
on the prior [independent author artifact audit](../fresh-project-author-independent-audit/README.md),
whose receipt and actual process exit it checks. For the peer it checks
frozen source files and historical Git blobs, compiler and provider pins,
actual objects and logs, each direct input, companion guards, output inventory,
Foundation artifacts and the exact four endpoint axiom reports. It also checks
the two siblings' output objects are not hardlinked and verifies the captured
coordinator output and exit against the pinned pair state.

The [receipt](receipt.json) records the actual coverage and hashes; the
[terminal observation](terminal-observation.json) records this audit's actual
process exit. The checker exercises rejection of a missing row, a forged
endpoint report, and optimized Python. It hashes at 8 MiB/s to reduce I/O
pressure and does not itself rerun Lean.

The pair uses the historical snapshot: both recorded 15 workspace-source
drifts. Direct inputs and guards do not fully authenticate package-transitive
or dynamic ancestry or mutations between observation points. The Foundation
provider's inner Lake exit was recorded, but its outer wrapper exit was not
observed. A matched historical pair does not, by itself, establish an AQ22
extension or that the displayed equation has an internal PRA proof.

The audit requires the pinned temporary source, build and provider trees. Run
at low priority with ordinary Python after preserving and moving aside only
this packet's receipt:

```sh
ionice -c 3 nice -n 19 python3 Computability/DiophantineConsistency/reviews/fresh-project-pair-independent-audit/audit.py
```

The script refuses to overwrite its receipt and rejects optimized Python.
