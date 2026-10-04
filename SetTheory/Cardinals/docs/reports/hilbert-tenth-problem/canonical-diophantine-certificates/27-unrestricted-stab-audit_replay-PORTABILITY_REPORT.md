# Portability verification

Date: 4 October 2026. Verdict: **PASS**.

The independently authored adapter `replay_audit.py` has SHA256 `c638da152240ce548d04cc99ae8c09df8281cec1fadefebb8fac89818bb198c1`.

The adapter preserves and executes byte-identical copies of the frozen exact, semantic and mutation audit programs. No source substitution, AST edit, scientific constraint change, submitted-builder run, author-checker run, upstream schedule or Lean run occurs. The only historical data access is the mutation harness's one known DAG `Path.read_text` call; it is redirected to the explicitly pinned bundled DAG with no old-path fallback. The exact checker uses its existing command-line path arguments. All workers and twenty mutation children run with Python isolation.

## Tests performed

1. Ordinary replay regenerated all three frozen scientific receipts byte-for-byte
2. A tar fixture was extracted at an unrelated path; the first fixture was removed before replay
3. The extracted input tree was made read-only, with files mode 0444 and directories mode 0555
4. Replay from `/tmp` succeeded on that moved read-only tree, again regenerating all three exact receipts
5. Complete before/after inventories, SHA256 file hashes, sizes, file/directory modes and nanosecond modification times matched
6. Success metadata contained no host-specific `/workspace/` path; all input and output references were relative to their stated roots
7. Existing, inside-bundle, ancestor-of-bundle and symlink output destinations were rejected
8. Tampered DAG, checker and expected receipt were rejected before scientific execution
9. Symlink and nonregular input-tree members were rejected
10. Preservation-predicate challenges detected file-byte, file-mode, file-mtime, directory-mode, directory-mtime and inventory changes

The test suite was then rerun using the parameterized development runner against the previously extracted read-only input. It again passed both ordinary and relocated/read-only replays and all guards, while preserving that source tree. The development result is `portable-test-results/portability-receipt.json`, copied unchanged to the release-facing `portability-receipt.json`.

These tests used a minimal fixture containing all pinned replay inputs. The adapter's whole-tree snapshot mechanism also covers additional regular release files. The final Report54 release should run the same adapter once against its complete assembled bundle before sealing; that final-bundle run belongs to release QA.

The normal replay command is:

`python3 -I audit_replay/replay_audit.py --output /absolute/fresh/external/directory`

The output `replay-receipt.json` is written only after pinned inputs, regenerated receipts and whole-bundle preservation all pass. No frozen scientific file was modified during adapter development or testing.
