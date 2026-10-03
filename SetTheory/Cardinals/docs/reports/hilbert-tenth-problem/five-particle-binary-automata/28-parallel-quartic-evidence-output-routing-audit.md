# Output-routing static audit

Date: 2026-10-03 13:34 UTC (static observation before final source sealing)

## Conclusion

PASS: exactly four Python scripts changed. Removing the exact new argparse block, restoring only output-path bases, and restoring the audit receipt basename reproduces each original script byte-for-byte. Therefore no mathematical test body, predicate, loop, fixture-handling code, receipt payload, counter, serializer, or compiler/circuit logic was altered. Both versions of all four scripts parse successfully with Python ast.parse. No target script or source module was executed or imported.

Compared current tree: parallel-diophantine-certificate-research-20261003
Against immutable backup: parallel-diophantine-certificate-research-20261003-v1

## Exact diff classification

- All four scripts: add argparse import, parser, optional --output-dir (Path, default adjacent script directory), argument parsing, path resolution, and mkdir(parents=True, exist_ok=True). Relative supplied output paths resolve relative to the invocation working directory. Existing adjacent-script roots remain unchanged.
- test_certificate.py: redirect exactly three explicit writes to OUT: example-pair-quartic.json, example-pair-sos.json, and normal/optimized receipt.json. The fixture read and fixture hash remain under ROOT. Certificate computation, artifact serialization, and receipt payload are unchanged.
- test_supplement.py: redirect exactly one receipt write to OUT; fixture read/hash and all checks unchanged.
- test_multisource.py: redirect exactly one receipt write to OUT; the source definitions and all checks unchanged. This script has no external fixture-file read.
- audit_emitter.py: redirect exactly one receipt write to OUT and select audit-emitter-receipt-optimized.json under python -O, otherwise audit-emitter-receipt.json. Source/hash inputs remain under ROOT; all checks and report payload unchanged.

## SHA-256: original → current

- test_certificate.py
  - Original: bbdb66dbf8c9014ffbd89c45b464f6aec432c0e2591426e1f932c95db2ac3403
  - Current: 84f335db791f01c3f31a5e9d2a583d16b973a944caa2f456a2a4e99f5ab3b4ad
- test_supplement.py
  - Original: 6923680162d762590013e408ba699bc445b3a47cbfdd01093af261b19f3dd41b
  - Current: 00acdc256b92b6306b1a4609cf67ee17ce54042a4ec397fc86f3dbd96d10cc34
- test_multisource.py
  - Original: 588822834b47d5f3ba8f13558c935c4bfc19db16f27de6da12eec8f822360216
  - Current: dad437dc85e7036070932c1a193e263b387f7c7220142506cdd923d560a8c655
- audit_emitter.py
  - Original: ecd46374b5bb5097b3efdf6473a0246a7fcaf59d20bb5105c2518c5250040695
  - Current: 27b1c293865e8317c271b57286e9faf7e07e5e6535eb5ccb44b75d92a6938f2e

## Unchanged core and Python inventory

- compiler.py, identical in both: 133d811972b6332ddc2fadfa8a7e34f3076b4712affa7c757d60e90d3ea2f5aa
- circuit.py, identical in both: dca31e8c2de8f6f4c1ae3bd17b8fbe614d67a92debd3b6b782f2d75704c83066
- All 12 other Python source files are byte-identical; no Python additions or deletions.
- lineage/v1-MANIFEST.json is byte-identical to the backup MANIFEST.json (SHA-256 dc2106553312d36cbcd655e5e3551e52771682de0a1f7f27e91798561ecf90a0).
- Initial whole-tree diff at approximately 13:31 UTC found only the four script changes and added lineage/v1-MANIFEST.json. Packaging metadata changed concurrently afterward: MANIFEST.json, PROVENANCE.json, README.md, SHA256SUMS, both bundle-verification receipts, and newly added REPLAY.md. The packaging review confirmed these changes are expected and outside this output-routing code audit. A separate review covered pending verify_example.py hardening and negative tests. These are not covered by this four-script audit. Inventory/hash claims above describe the observed files at audit time; no claim is made about later edits or whole-tree immutability before final sealing.

## Replay precautions and limits

- Static audit only; replay tests were deliberately not run before the source snapshot.
- Use python -B / PYTHONDONTWRITEBYTECODE=1 for replay. The new option redirects explicit writes but does not suppress Python import bytecode caches in the source tree.
- Use separate normal/optimized output directories to preserve both independently generated example artifacts; their basenames intentionally remain identical across modes.
- Omitting --output-dir preserves the old adjacent-script write destination, except the deliberately distinguished optimized audit receipt name.
- No source-tree files were written, no target modules imported, and no installations, uploads, upstream execution, or network actions were performed in this audit.

Portability note: absolute workspace prefixes in the two compared-tree labels were removed; audit findings and script hashes are unchanged.
