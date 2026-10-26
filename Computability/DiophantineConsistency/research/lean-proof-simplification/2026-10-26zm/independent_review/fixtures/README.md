# Frozen review fixtures

These are exact source/candidate snapshots solely for replaying the independent review. Original-source identities are pinned by `source_manifest.json`.

**WangTiles942PhysicalOrder is EXCLUDED as a duplicate of closing packets zh/zj.** Its source and candidate snapshots remain only to reproduce the correctness/comparison receipt; none of its savings is new.

FinBasic and Logic_Equiv_Defs are pinned Mathlib source, with binding receipts and the upstream Apache 2.0 license. They support only the excluded comparison candidate.

Sidon prior and round5 patches plus SidonPositions.original.lean make patch composition replay self-contained. No Lean compilation is performed by the Python scripts.
