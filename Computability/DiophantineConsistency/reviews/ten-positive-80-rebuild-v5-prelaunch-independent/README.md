# Independent static review: two-baseline v5 retry

The frozen `research/ten-positive-80-coherent-rebuild/run-v5.py` SHA `67f287a75d095fc45abde2d14acc732110956e3e248c154e817f92b14eb43558` adds one exact `ModelArithmetic` historical warning baseline to v4's already reviewed `ArithmeticPellPigeonhole` exception. Its separate outer wrapper SHA is `0d1b7d50fdf856c2e5f3f61e8a5f91004f4c5ef19a2295e148885bd7052e0d89`. Static review found no blocker to one coordinated **fresh attempt03**; this is not a completed rebuild or Lean replay.

V5's `diagnostics_allowed` accepts diagnostics only for the exact matching module, source SHA, and **entire** source-path-normalized combined log of one of these two individually pinned historical policies:

* `ArithmeticPellPigeonhole`, source `ebdbc22e239754f8f686be6971742d1b02560c9ffa35d464d2aecc323370765c`, baseline `1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92`.
* `ModelArithmetic`, source `2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6`, baseline `6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d`.

Each baseline is also tied to a separately pinned successful historical producer receipt and the same 127-source plan. Both contain exactly the previously observed three deprecation warnings and no error or `sorryAx`. The stopped attempt02 logs match them exactly after replacing only the copied source path. V5 records the appropriate exception when used; all other coded/uncoded diagnostics remain fatal.

`check.py` executes only the actual AST-extracted pure predicate, checks runner/wrapper, both baseline and receipt hashes, historical source/plan equality, and actual attempt02 logs. It independently rejects cross-baseline swaps, wrong module/source, added warning/error/`sorryAx`, changed or missing log text, and unrelated warnings; both exact logs and a clean log pass. It invokes the prior independent v4/v3 prelaunch plan and guard checks. The author's own predicate mutation check was rerun and passed. No full runner import, Lean or rebuild was performed by this review.

The v5 diff otherwise preserves the v4/v3 fresh temporary union, direct input and companion checks, outside current baseline, final source/header checks, 8-GiB sampled guards and atomic result capture. The wrapper refuses existing attempt03 paths, pins the runner before launch, records the actual child exit and runner hashes before/after, and returns the child exit. It has no global lock, and records rather than itself rejects an after-hash mismatch.

Require a final `PASS`, outer exit 0, all 127 outputs and serialized headers, both exception receipts if encountered, four endpoint axiom reports and independent post-run pin checks before treating the attempt as successful. Per-stage `RETURNED` is not itself acceptance. Historical package/transitive/dynamic ancestry, potentially undiscovered producer drift, and external JSON/PDF binding remain separate even after a successful partial-cone replay.
