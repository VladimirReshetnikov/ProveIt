# Source and artifact review of the checked MC assembly

The reviewed source states the closed, hypothesis-free Lean equality
`Nat.ofDigits 256 CompactLowByteRecipeData.bytes = CompactSymbolicPorts.lowNat`.
It supplies `all_windows` from the bounded `point` theorem and applies the
generic radix-window reconstruction using the separate upper bound. Its
fifteen interval branches and twelve boundary calls are consistent with the
previous independent [source and finite coverage review](../compact44-low-byte-assembly-source-review/README.md).
The corrected exponent rewrites are present in all four symbolic interval
branches. Factoring the gap and tail irregular-byte lemmas and increasing
heartbeats distinguish this successful source from the earlier draft.

The single-author successful receipt records Lean exit 0, no warnings or
`sorryAx`, and the two named metatheory reports
`[propext, Classical.choice, Quot.sound]`. This review independently checks
the exact source, compiler log, live object and direct/companion guards. It
also checks all twelve boundary receipt/source/object/log links against the
selected overlay, including the corrected boundary 01. The selected closed
byte-recipe object is linked back to its own source and successful receipt.

The prepared union records 28 provider roots, 1,468 inventoried provider
files and 606 selected files. This review rechecks the full selected path
set, selected hashes and targets, the recorded provider inventory, and the
524 overlapping relative paths; no mismatched common file hash was found.
There were no suppressed companions in the manifest. These are sampled
filesystem and selected-provider checks; they do not authenticate all
transitive, package or dynamically loaded ancestry and are not a new Lean
replay or paired build.

The equality is to the closed Lean byte recipe. Correspondence between that
recipe and the retained parent `MC.bin.gz` is an **external** finite and
filesystem/gzip provenance check, independently repeated in the preceding
source review. No Lean theorem here identifies filesystem bytes or proves a
PDF transcription, another port equality, or an iPRA endpoint.

[`audit.py`](audit.py) performs the read-only checks; [`capture.py`](capture.py)
retains source/object/receipt hashes, all twelve boundary receipt summaries,
the outcome and terminal receipt under [`observations`](observations/).
The live selected `/tmp` objects and inherited providers are needed to rerun
the audit. No mismatch was found within the stated scope.
