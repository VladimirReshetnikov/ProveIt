# Independent review: accepted conjugacy aggregate retry

The aggregate retry has an author-recorded successful outer runner exit and seven Lean axiom reports. `check.py` independently checks the accepted `outer-attempt01` wrapper receipt, wrapper and runner hashes, outer output hashes, inner `directbfsaggregateretry-attempt01` receipt, source/copy/output/log hashes, unchanged pre/post pins and import snapshots, all 60 first-selected direct imports and their object hashes, all 59 stage-receipt hashes and the complete previously independent full01 audit. It checks the seven exact `[propext]` reports and absence of errors, warnings and `sorryAx`, and the recorded process/memory samples and Lean flags. Exact 60 selected provider paths/hashes and outer/inner receipt hashes appear in `check-output.txt`. This is not an independent Lean replay.

The outer wrapper receipt records exit 0 for `run.py` SHA `1bc094f1934b8df7b54f0e7bfbadfba8c2b95cc30c0038dca5c5952761e705ef`; its source SHA is `3439657a35a3817564113158e9a4b155a19e7801b725ea2bfe4eda7d23bda47b`. The accepted object is `/tmp/direct-bfs-aggregate-retry-ej6z9xcm/DirectBFSCoverageAggregate.olean`, SHA `1e8286158838654f19d7de3ba4ca45b99b72eda814546188e0a982b6c84af02b`. The inner terminal alone precedes final runner checks, so the outer exit is essential. The wrapper and receipts remain author-produced process evidence; this review independently verifies their current files and consistency, not a new kernel execution.

The source combines the 59 frozen direct range modules into these seven Boolean statements, each recorded with axiom list `[propext]`:

* `rows_all`: `checkRows 0 943=true`, the selected original-to-direct row-renaming check on indices 0–942.
* `inverse_all`: `checkRowInverse 0 943=true`.
* `horizontal_all`: `checkHorizontal 0 250=true`.
* `vertical_all`: `checkVertical 0 439=true`.
* `inversebounds_all`, `horizontalbounds_all`, `verticalbounds_all`: both corresponding forward and inverse arrays are in range at each index in the respective 943, 250 and 439 domains.

The separate prelaunch review `reviews/direct-bfs-conjugacy-full-sweep-independent/` records exact range coverage and the 265 successful individual no-axiom range reports; `reviews/direct-bfs-conjugacy-aggregate-retry-independent/` records the seven tactic-only changes from the failed aggregate source. Other finite shape/color checks and their connection to these Boolean statements are separate. This aggregate does not by itself produce a model-level bijection or tiling lift, a machine halt implication, external JSON/PDF coefficient identification, or a syntactic iPRA proof. Direct provider pinning does not establish complete transitive selection, source-to-object, package or dynamic-library provenance.
