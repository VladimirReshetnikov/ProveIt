# Phase-eight upstream Rocq boundary

The read-only census compares current commit `d726d1dfe7aa0b46b46da3e2bb8c96ba4ab0d73d` with upstream `9bac1c403c780dee62206556fbda311236798c98`. All 31 changed paths fall into exactly two classes: 27 Rocq production paths and four `normalized-91` receipt paths. No Lean production path is changed by this upstream delta.

`retained-production.json` records both commits' exact Git blobs, modes, raw SHA-256 hashes and sizes, including absences. Preserve its 19 current production files and eight current absences. These 27 entries exactly match the earlier phase-seven retained-production boundary. Accept the four receipt paths verbatim from upstream. The census independently checked all 31 current worktree states against the current commit; `before-check.json` additionally checks the index and modes. The phase-eight Lean changes are outside this manifest and are neither reverted nor audited here.

The new receipts report an upstream Rocq 9.1 compilation and recursive checker result, rather than this session's Lean phase-eight execution or adoption of the normalized Rocq production tree. All 44 supplied compiled-source SHA-256 values match the upstream `coq/215` files. Both supplied text logs are committed with LF line endings, while their recorded verification hashes match the corresponding CRLF byte streams exactly. Their committed raw hashes and reconstructed-CRLF comparisons are recorded separately; no payload is rewritten. This is a source/log identity observation, not an independent replay of the supplied compiler or checker.

After root performs the merge and restores the production boundary, the read-only check is:

```sh
python3 -B check_boundary.py --repo /absolute/path/to/Proofs \
  --manifest retained-production.json --phase after
```

That check requires exact worktree bytes, modes, staged blobs and stage-zero entries for all present paths, and both worktree/index absence for the eight retained absences. It performs no restore, staging, commit or compiler action. `inventory.py` is the reproducible original census; use the two immutable commit IDs and a fresh scratch output path.

The first census attempt assumed raw log hashes would match the supplied record. That assertion failed; the original source/stdout/stderr are retained under `history/strict-raw-log-assumption`. The successor reports the exact LF/CRLF distinction instead of relabelling the raw payloads. No source, receipt or Git state was changed by either attempt.
