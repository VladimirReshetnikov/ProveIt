# Structural reductions for Diophantine consistency equations

Round eleven, 24 October 2026. Reviewed ProveIt main commit: 2605669a532342f153b13eb6b4a0af4b54f5fa37.

Main result: lucas_h1868/integer10.json is a fixed ordinary polynomial in ten unrestricted integer variables, exact degree 1,245,324, with 480 live binary operations. The change combines a new norm-saturation argument with certified source packing and an exact shared-power plan. lucas/ retains the simpler unchanged-prefix saturation control: degree 1,248,364 and 481 operations. The preceding equation had degree 1,576,864 and 481 operations.

Completed companions:
- positive/p11_degree277.json: 11 strictly positive variables, degree 277, 111 operations.
- positive/p12_degree78.json: 12 strictly positive variables, degree 78, 101 operations.
- positivity/: two 37-integer quartics; 30-integer sextic; 26-integer octic; 25 integers at degree 10; 24 at degree 12; 23 at degree 16.
- commutative/: proved height-register source, with local natural-witness/degree tradeoffs 20/50, 21/20 and 23/14, one bounded block instead of two. These are NOT full consistency-equation counts. All three Lean constructors are uncompiled; the global polynomial is not materialized.
- packing/factor_gap/: exact positive source simplification from 86 weighted records to 85. No improved final endpoint is asserted for it.

Read report/report.pdf or rebuild the editable report/report.tex. Full component proofs and independent audit narratives accompany the literal equations. All nonvariable symbols in the equations are explicitly fixed payloads or polynomial abbreviations. MF ports are already shifted and must not be shifted again or mixed across source tuples.

## Verification

Byte-identical replay was validated on Linux with Python 3.12.14, SymPy 1.14.0 and zlib 1.3.2, as used for the delivered coefficient compression. Other versions or platforms may regenerate mathematically equivalent payloads with different gzip bytes, causing the strict byte-comparison gate to fail. Use the validated environment for exact byte replay; the mathematical checks are separate from compression-byte identity. No network is needed. From the extracted root:

    python3 verify.py

The default verifies every shipped SHA-256, copies the packet to isolated temporary directories, runs the authored allowlist in normal and optimized Python, compares every specified rebuilt literal/coefficient/constructor byte for byte, and runs corruption controls. It does not modify the delivery copy. Optional --quick runs normal Python only; --manifest-only verifies only the inventory. --output /absolute/path/outside/the/archive.json saves a receipt without mutating the release. REPLAY.json is the exact command and generated-output contract.

No upstream program, coefficient generator or proof checker is executed. Retained upstream Python files are inert provenance. Independent coefficient reconstruction is implemented in low_degree_audit/audit_literals.py. Its --release mode rechecks retained member bytes against the previous full-archive audit receipt; it does not authenticate omitted ZIP bytes again. Full intake archive hashes and member mappings remain in low_degree_audit/SOURCE_ARCHIVE_PINS.json and ARCHIVE_MATCHES.json.

The mathematical proof is not replaced by these finite checks. In particular the full equation proves |C|>1 before applying the saturated Lucas theorem; the standalone theorem without that guard is false. The checker includes a concrete exceptional-index countercontrol.

## PDF rebuild

Run sh report/build.sh. A standard TeX Live installation with pdfLaTeX, Latin Modern, amsmath, amssymb, amsthm, booktabs, longtable, array, geometry, microtype, hyperref and enumitem is required. The script supports this delivery environment's explicit TeX search paths and creates report/texcache plus ordinary TeX build intermediates. Rebuild in a working copy, not the immutable release if you want verify.py inventory verification to remain exact. PDF byte identity across TeX distributions is not asserted; the mathematical literal artifacts are byte-reproducible.

## Inventory and permissions

MANIFEST.json is the exhaustive shipped-file list with size, SHA-256 and role. MANIFEST.json does not hash itself. DEPENDENCIES.md maps the inherited mathematical interfaces. Historical source documents preserve their original relative references; they do not promise the whole original repository is vendored. New operational instructions here refer only to shipped files.

New AI-assisted work: LICENSE.NEW. Reused sources: their retained licenses and notices, as detailed in NOTICE.md and the manifest. No claim of global minimality, historical priority or a new end-to-end kernel certificate is made.
