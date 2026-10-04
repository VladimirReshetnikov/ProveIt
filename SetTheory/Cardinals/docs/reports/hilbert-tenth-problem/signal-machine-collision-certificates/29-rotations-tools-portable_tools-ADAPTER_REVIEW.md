# Portable family59 replay: adversarial review

Status: **ACCEPTED after amendment**. No remaining must-fix findings for the stated stable-tree, trusted-runtime scope. All three initial findings below were fixed and independently retested.

## Scope and execution boundary

Reviewed `portable_tools/replay_family59.py`, `portable_tools/test_replay_family59.py`, and the two authenticated owned independent checker sources. Ran only inspected owned replay/test code and newly written safe QA. The science constructor, upstream programs, and Pell source remained inert. No files in the frozen 60-file science packet or 9-file audit packet were edited.

## Resolved findings in the initial revision

1. **Medium: symlink-bearing paths can bypass rejection through lexical normalization.** `explicit_path()` called `os.path.abspath()` before examining components (initial lines 72–79). A dangling `link/../packet` was accepted as its real sibling `packet`, even though the supplied path did not exist. The same flaw applied to output paths. A guarded full CLI replay returned PASS and created the normalized output. Content pins remain effective, but the promised fail-closed path policy is not met. Reject `..` before normalization or inspect unnormalized components without following symlinks. Evidence: `adversarial-review/PATH_ALIAS_REPRO.json` and `PATH_ALIAS_FULL_REPLAY.json`.

2. **Medium: the test harness can write inside an input tree.** Its `--work-dir` was created before validating disjointness (initial lines 61–66). Supplying a work directory below `--packet` created `work/tools/replay_family59.py` and other directories in that input before failure. Reproduction used empty synthetic roots only. Validate all input/work roots and reject overlap before any mkdir/copy. Evidence: `adversarial-review/HARNESS_OVERLAP_REPRO.json`.

3. **Low: a negative test checks the default output, not an overridden output.** Initial line 116 checked `out` even when `--output` was replaced. A write to the effective output followed by rejection could therefore go unnoticed. Check the effective output and unchanged pre-existing targets, or snapshot the entire negative case before/after execution.

## Verified integrity and replay properties

- All four replay roots are required; normalized roots are checked for overlap and output must be absent.
- Manifest and audit-receipt trust anchors authenticate complete inventories, including rejection of extra files/directories. Dependencies are authenticated against pins inside the authenticated packet.
- Both checker source hashes are fixed before AST compilation. Only the static checker's ROOT/OUT and geometry checker's OUT assignments are changed in memory; preserved source bytes are never rewritten.
- `compile(..., optimize=0)` retains checker assertions under `python -O`.
- Four regenerated artifacts must match the frozen audit outputs byte-for-byte. A fifth replay receipt is emitted only after all checks pass. Packet/audit/dependency bytes, modes, and mtimes are compared before and after.
- Historical dependency paths in reproduced receipts are inert metadata; no fallback read appears in inspected code.
- An independent fresh run passed all 3 relocated read-only replays (including `-O`) and all 32 existing negative controls. Output hashes matched across runs. Evidence: `adversarial-review/full-tests/PORTABLE_TEST_RECEIPT.json`.

## Final amended verification

- Inspected final changes: parent traversal is rejected before normalization; the harness rejects symlinks/traversal and overlapping roots before any mkdir/copy; negative controls snapshot default, effective, and normalized output targets.
- Fresh independent final suite: **3/3 relocated read-only replays, 39/39 adapter negative controls, and 3/3 harness work-overlap controls passed**. Includes Python `-O`; all five replay output hashes were identical across positive runs.
- Re-ran both original input/output alias regression cases: both reject before output creation.
- Reviewed final empty-path hardening: adapter and harness reject empty arguments before `Path`/`abspath` can select the current directory; the negative-test output snapshot does not treat an empty argument as cwd. Four additional CLI negatives and direct adapter/harness empty-path checks passed.
- Original frozen inputs were preserved by the final suite; science/upstream/Pell code was never run.
- Evidence: `adversarial-review/final-empty-path-tests/PORTABLE_TEST_RECEIPT.json` and `adversarial-review/FINAL_REGRESSION.json`.

Final reviewed SHA-256:

- Adapter: `7787803602c1693899561dd6ed6201fc17aadddeb93afdcff9bada94fddc1535`
- Tests: `fa49ec964814daf9182fedfb3da337ef1bc0c78dcb201aca739661fde3c26de7`

Initial revisions, retained only in reproduction evidence: adapter `3e6c35a41cac6d3b380747f7e668510afa3f7968ba40787e6a40b8d70aaa9439`; tests `a9157b0a9fe861b2a325f8ebdfea711b19f36dfa23eac961147e690c29205767`.

## Limits

This is a reproducibility/integrity review for stable local trees in a trusted Python/stdlib/SymPy environment. It is not an OS sandbox or a defense against concurrent filesystem replacement. The audit hook blocks the documented open/socket events; it does not independently confine every OS operation. Preservation evidence concerns bytes, modes, and mtimes, not access times. Successful replay does not expand the mathematical claims of the frozen independent audit.
