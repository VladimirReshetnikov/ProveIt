# ProveIt Lean proof simplification review 5

Read report/proof_simplification_report.pdf or rebuild its editable TeX with bash report/build.sh.

Three small selected families remain after the closing exclusion screen: S (Sidon injectivity endpoints), O (controller order-one endpoint reuse), D (definitional iterator depth). They save 4+3+2=9 physical source lines. See candidate_status.json for exactly which patches are selected. Five theorem endpoints are changed across three modules.

F (finite physical-order rigidity) was an exact duplicate in a newly placed prior packet. Its replacement file/patch and model checks remain as EXCLUDED COMPARISON EVIDENCE ONLY. Do not interpret local_candidates/metrics.json's original 30-line shortlist total or independent_review's 33 reviewed source-line delta as new savings. Only the explicit selected total of nine is claimed.

Sources are pinned at e1c8914bc7064d9a8e7c06171a18069a949badd0. The one closing collection screen is pinned at 91dce223cda86c0755b8a9b2504f84be04443fce. All prior collections and earlier delivered rounds are assumed applied. This is a semantic assumption, not a claim all prior patches form one compatible checkout. The particular old Sidon moment patch was composed in both orders and verified byte-identical; relative to that concrete prior baseline Sidon is 161→157, not 168→164. The old seven-line saving is not reclaimed.

All Lean candidates are UNCOMPILED. Lean/Lake were unavailable and were not installed. This archive is a focused source snapshot, not a full Lake checkout. Source hashes, Python tests, exact patch replay, finite models, and PDF rebuilds are not kernel proof checking. No upstream changes were made.

Offline commands:

    python3 verify_bundle.py --strict
    python3 provenance/verify_snapshot.py
    python3 -m unittest discover -s validation -p 'test_*.py'
    python3 -O -m unittest discover -s validation -p 'test_*.py'
    python3 controller_order_review/verify.py
    python3 independent_review/check_sources.py

Some scripts write regenerated receipts or __pycache__ files. Run them in a disposable extraction and use PYTHONDONTWRITEBYTECODE=1 when checking exact bundle inventory afterward. To regenerate candidates, copy the extraction first and run local_candidates/build_candidates.py. The full modules and patches must reproduce exactly.

Future Lean integration gates and stale-.olean precautions are in validation/LEAN_REPLAY.md. O routes through stronger exact-order results: it is a maintenance option, not a dependency or performance optimization. No equality of before/after axiom footprints is claimed.

The provenance snapshot binds 697 current sources, 27 direct external dependency files and 32 predecessor files. Dependencies are not a transitive closure. Baseline evidence includes curated manifests and excerpts; raw fetched archives, private upload helpers and rendering intermediates are not deliverables.
