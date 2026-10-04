# Portable adapter QA

Date: 4 October 2026. Result: **PASS**. The original frozen science and independent-audit bytes remain unchanged.

## Positive replay

The freshly inspected test harness copied the complete science and audit trees, placed the adapter beside them, archived the fixture as ZIP, extracted it to a fresh directory, and moved the entire extraction to a nested path containing spaces. It changed every science/audit file to mode 0444 and every directory to mode 0555. The adapter was then run normally and with optimized Python, with separate new external outputs.

Each adapter run executed both original independent checkers normally and optimized, using `-I -S`, their unmodified pinned source bytes, and an explicit path to a newly made read-only science snapshot. All generated source/interface receipts equalled the frozen receipts byte-for-byte. The two outer replay receipts were identical. Every output manifest entry was verified. The original inputs and moved read-only copies preserved all bytes, modes, modification times, identities and directory inventories measured by the harness.

A separate direct run against the original explicit paths also passed, writing only to a new external output.

## Negative replay: all 28 rejected

1. Missing required arguments
2. Relative input path
3. Missing input directory
4. File supplied as an input directory
5. Identical/overlapping input roots
6. Swapped science and audit roots
7. Parent-directory traversal
8. Symbolic-link input root
9. Symbolic-link input ancestor
10. Altered polynomial DAG
11. Altered science manifest
12. Altered independent checker
13. Altered expected audit receipt
14. Altered independent-audit manifest
15. Symbolic-link input file, even with identical target bytes
16. Symbolic-link audit manifest
17. Symbolic-link science subdirectory
18. Missing manifested science file
19. Unmanifested science file
20. Unmanifested audit file
21. Unmanifested empty science directory
22. Output inside science
23. Output inside audit
24. Existing output directory
25. Existing file as output
26. Symbolic-link output
27. Symbolic-link output ancestor
28. Missing output parent

Every invalid request returned a nonzero exit with the expected guard diagnostic. No invalid request created a new output directory. Existing output/symlink targets were checked for preservation.

## Boundaries

The adapter authenticates the exact frozen packet, not arbitrary future versions. Its input manifests are independently pinned in the adapter; edits to a manifest cannot authorize a changed checker or polynomial. It executes only the two authenticated independent checkers copied under the new output. Author/build/upstream scripts and saved accepting schedules remain inert.

The portable adapter does not change the accepted conditional mathematical scope. The original audit's source reconstruction and matrix-interface checks are replayed; no Lean rebuild, full gigantic Pell witness, historical acceptance trace, or arbitrary-program compiler is newly claimed.

The test harness is an independent newly written replay test, not a formal sandbox verification. The adapter's guards do not claim race-proof protection against hostile concurrent directory replacement or a compromised interpreter/adapter. Relative paths, symbolic links, traversal, altered bytes and unsafe output reuse are explicitly rejected for the supported static-filesystem workflow.

The QA receipt is `qa-receipt.json`; core adapter code is `replay_audit.py`; the reproducible test harness is `test_replay.py`. All three are bound by `release-files.json` and should also be included in the final release manifest.
