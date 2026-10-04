# Sealed portable replay, 4 October 2026

The unchanged scientific audit checker is reproduced successfully by the release adapter. The source proof packet and original independent audit remain frozen. This release adds only authentication, relocation, execution and comparison infrastructure.

## Final validation

* `TEST_RESULTS.json`: 27 passing cases, including three successful replays, read-only relocation of inputs, full read-only relocation of adapter plus inputs, and rejection/regression cases
* `READONLY_REPLAY_RECEIPT.json`: successful complete read-only relocation, with deterministic evidence equal byte-for-byte
* `FINAL_REPLAY_RECEIPT.json`: final successful authenticated replay against the original roots after independent review
* `independent_review/REVIEW.md` and `REVIEW_RECEIPT.json`: accepted, no remaining blocker under the documented trust assumptions
* `independent_review/PROBE_RESULTS.json`: nine additional adapter-negative probes and independent repetitions of the two harness regression checks; these are 11 supplemental checks, not 11 additional distinct release-suite cases
* `independent_review/FROZEN_PRESERVATION.json`: independently recorded before/after frozen-input preservation

The review identified two test-harness defects before release: a symlinked work-parent could cause fixture creation inside an input copy, and optimized Python could remove assertion-based verdict checks. The final harness rejects both before creating work. Both fixes were independently regression-tested. The core replay adapter, scientific checker and scientific proof required no change for these findings.

## Packaging

Keep this adapter directory complete when distributing its own manifest. The separate science and audit roots must also remain complete and byte-identical to their pins. They can be placed at any canonical absolute paths; pass those paths explicitly. For example, an evidence release may use `science/frozen-proof`, `audits/scientific` and `tools/portable-replay`. Choose a fresh output directory outside all input roots and the adapter directory.

The nested independent review is self-contained. Its `review_probes.py` is historical diagnostic source with environment-specific run paths, not the portable replay entry point. It is not executed by `replay.py` or `test_replay.py`. Deliberately malformed local review fixture trees were excluded from this release.

## Boundaries retained

Only the reviewer-owned checker is scientific executable payload. All author code and copied dependency material stay inert. Evidence JSON comparison is exact; stdout is compared exactly against its new output-path-specific expected bytes. Python isolation is not an OS/network sandbox. Trusted Python/standard library and a quiescent filesystem are required. See README.md and the independent review for the full limitations and unforced postexecution error branches.
