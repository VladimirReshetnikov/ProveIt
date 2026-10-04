# Complete literal-ant certificate: recovered science edition v2

This reconstructs the science packet after the 4 October 2026 filesystem reset. Read RECOVERY.md before interpreting old and new hashes. The two canonical arithmetic streams are freshly verified identical to their pre-reset audited targets; enclosing implementation, prose, receipts, manifest and archive have new byte identities.

## Exact results

Two ordinary positive raw inputs: 465 positive witnesses; 285 component residuals; one paid sum-of-squares equation; 2,307,457 operations = 1,153,586M+1,153,871A; exact degree 2,304,000.

One ordinary positive raw input via paid Cantor pairing: 467 positive witnesses; 286 residuals; 2,307,467 operations = 1,153,590M+1,153,877A; the same degree.

The separate strict literal-1/3 coefficient prefix costs 554,386,261,707,905,131 operations. Full strict totals are 554,386,261,710,212,588 and 554,386,261,710,212,598. This deliberately unoptimized certificate is not an operation record.

The raw language is U15 J1 halting as represented by a pinned initialized periodic-ant accepting observable. The ant continues moving. All inherited Pell/history, recoder, literal simulation and published machine-compilation theorems are explicit dependencies; finite regressions are not replacement proofs.

## Files

- PROOF.md: complete iff argument, all-positive port ledger, soundness order, converse, paid pairing and exact degree
- STRICT_GRAMMAR.md: every fixed coefficient and every literal-1/3 construction loop
- merged_source.py: complete new recovered topological arithmetic generator
- two-input-receipt.json and one-input-receipt.json: complete counts, witness names, gate intervals and old-stream comparison
- history/: byte-identical recovered174-node source, rebuilt own exact/finite checkers, domains and data-only pinned upstream proofs
- audit_recovered_stream.py and independent-stream-receipt.json: new independent serialized-stream parsing, topology, counting, domain, coefficient and SOS checks
- check_exact_degree.py and degree-receipt.json: new independent sparse highest-homogeneous calculation
- check_output_boundaries.py and output-boundary-receipt.json: fresh external-output guards and early optimized-mode rejection
- one-input/AUDIT.md: freshly rechecked primary two-sided U15 encoding
- SOURCE_PINS.json and RECOVERY.md: precise recovery provenance

## Fresh independent recovered audit

independent-audit/ contains the original auditor's newly reconstructed and rerun observer, exact history-polynomial transcription, exact recoder leading-term check and bounded arithmetic tests. Its 15-file packet is copied unchanged and hash-pinned. The old full streams are recovered identically; audit implementation/prose/archive bytes are new. For disposable audit replay, set ANT_CERTIFICATE_ROOT to the current science root; all four checkers suppress bytecode. Read independent-audit/AUDIT.md for exact scope.

## Read-only replay

After authenticating the enclosing manifest against the trusted externally supplied digest, inspect the own-code replay closure. Main replay needs only Python's standard library:

    python -I -B verify_packet.py --manifest-sha256 TRUSTED_DIGEST

It checks all manifest files, both complete generated receipts, the exact degree calculation, and output-boundary behavior. No packet file is rewritten. It rejects optimized Python. For full independent stream checking:

    python -I -B audit_recovered_stream.py

For a new receipt and optional expanded source:

    python -I -B merged_source.py --output /tmp/new-two.json
    python -I -B merged_source.py --arity 1 --output /tmp/new-one.json
    python -I -B merged_source.py --output /tmp/new-receipt.json --emit /tmp/new-source.jsonl

Every destination must be fresh and outside the resolved source tree. Both destinations are checked before either is created; existing files, duplicate paths, dangling symlinks and source-tree symlink aliases are rejected. --emit writes all approximately 2.3 million arithmetic gates. Without it, every gate is still generated, validated, counted, hashed and degree-checked.

The emitted schema declares positive raw and existential coordinates, then numbered +,-,* gates. Integer operands mean earlier gate IDs; C: labels name fixed coefficients. residual_pair rows store expression pairs without asserting them. The sole assertion is the final [eq,F,C:0]. The coefficient ledger includes zero from that assertion. Gate outputs never add existential coordinates.

History symbolic/finite checks require SymPy. Run history/reconstruct_history.py and history/audit_history.py only in a disposable copy, because their command-line entry points regenerate their receipt files. Both normal and optimized history runs are supported; the three complete-source/replay/output-guard tools reject -O as intended.

No code under dependencies/recipe_assets or history/source is a replay entry point. Those files specify mathematical dependencies and fixed coefficients, and are never imported or executed. This recovered packet is a compact composition addendum, preserving the corrected horizontal geometric-repunit multiplier.
