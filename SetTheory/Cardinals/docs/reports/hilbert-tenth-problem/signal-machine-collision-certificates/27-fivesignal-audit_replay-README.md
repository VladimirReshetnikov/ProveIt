# Portable independent-audit replay

This adapter replays only the two independently authored exact checkers from the frozen five-signal audit. It does not execute the construction author's emitter, membership checker, saved physical word, or any physical simulator. The original checker files remain unchanged.

## Files to package

Copy the complete original frozen directory `five-signal-obstruction-independent-audit-20261004` into the report packet, preserving every byte. Its `MANIFEST.json` SHA-256 is:

    faf598b0cbbce38d618e40642b486f98a36671b48a71284ca9257d4684b5a390

Copy the four files in this deliverable directory alongside it or under a tools directory:

- portable_audit_replay.py
- README.md
- ADAPTER_TESTS.json
- EXPECTED_PORTABLE_REPLAY_RESULT.json

Do not package the temporary test directories adjacent to this deliverable. They include a deliberately corrupted test copy, used only to establish fail-closed behavior.

The adapter SHA-256 is:

    ae62266461de1dfbe6b22bf6cb7120bc86cb8261d1fea84ccd21a41d8d777ef2

## Command

From any directory, with Python 3.9 or later and no third-party dependencies:

    python /path/to/portable_audit_replay.py \
      --audit-packet /path/to/report/independent-audit \
      --output-dir /path/to/brand-new-replay-output

The audit-packet argument names the directory containing the frozen audit MANIFEST.json. The output directory must not exist and must be outside that audit directory. It need not be adjacent to the packet. No original workspace path is required. Run without `-O` or `PYTHONOPTIMIZE`; the adapter rejects optimized Python because the checkers use assertions.

## What changes in memory

Both checkers were inspected in full. Their only input locations are SRC and their only writes are under OUT. After checking exact source bytes against hardcoded SHA-256 values, the adapter performs exactly these two literal replacements, each once per checker:

    OUT=Path(__file__).parent -> OUT=Path(__audit_output_dir__)
    SRC=OUT/'inert_sources' -> SRC=Path(__audit_input_dir__)

In the inert-rules checker, the existing trailing `/'RULES.json'` remains unchanged. The replacement path variables are supplied by the adapter. No arithmetic, guards, checks, templates, assertions, or output formatting are changed. The rebased checker-text hashes are recorded in the replay result and are independent of the machine's absolute paths.

This is a hash-pinned integrity/reproducibility adapter, not a general sandbox for arbitrary code. It refuses modified source bytes. It executes the two approved checker texts in memory; it never imports or invokes the author's code. The supplied rational_membership.py is checked as an inert file only.

## Exact expected comparisons

Before execution, the adapter verifies the frozen manifest and every one of its 13 listed files. After execution, the following outputs must be byte-for-byte equal to their frozen counterparts and match these hashes:

| Output | SHA-256 |
|---|---|
| exact_algebra_receipt.json | 4576156d03853c41c290173481f0bfe51e81c54ae470f70d9491e387b6b94cf8 |
| inert_rules_receipt.json | fdbf73c7b724d5148b3f76b0fd0c587924dd8e7a39ac2b90f4a45a62287bfc14 |
| all_138_local_rule_checks.tsv | 95621369af4eb77b8df700986114315f6c2cf1673e964ae910bdaef1e9273031 |
| exact_algebra_stdout.json | adf68833fd10b4755a90e10bb1e48aa956cc25da412373d32a94a2e849139039 |
| inert_rules_stdout.json | ebab105dc2fd66e6911900802c75a8bcec1fe63b6115c9269cd476af50ebac6d |

The entire frozen audit packet is checked again before a PASS result is written. A successful replay creates those five files and PORTABLE_REPLAY_RESULT.json only inside the designated new output directory. Its summary must equal EXPECTED_PORTABLE_REPLAY_RESULT.json byte-for-byte.

Original-location and relocated-copy replays both passed, with identical results. A deliberately modified GUARDS.txt was rejected before output creation; an existing output directory was refused; optimized Python was refused. ADAPTER_TESTS.json records these checks.
