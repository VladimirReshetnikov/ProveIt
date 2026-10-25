# Separate ROOT release of the corrected grouped66 r2 pipeline

ROOT explicitly releases the following ten sequential commands only after
reading both complete static PASS reports committed in49abe04766. Exact
HOLD: `a0513986f47855fba3c8c9321e0ad0f32daf7fdf6c539958c0c9422f81ef9f79`.
SOURCE_PINS: `7b7cf245765f9794dd7cffd1ca086e5808e7ff13e6fe983b752b2b6e315799e2`.
The16 local held payloads and9693-byte outside renderer remain frozen.

- `one-page-grouped66-static-r2-root.md`: `cd5ba191d797f507cf750e6379838115428896adbd547d80b8d641f764079fb5`.
- `one-page-grouped66-static-r2-root.json`: `2c5225d2c9d2da29f4055e8704fec9c2b371ef80a32a3ecbf08f2e2d6955c6d2`.
- `one-page-grouped66-static-r2-peer.md`: `40351eea39fd0de1ea832e349c88ac54cdc7f2a3fe2b3e962f5f6fd1bdb613a3`.
- `one-page-grouped66-static-r2-peer.json`: `8065c25be4bc788fdea2db231c4abfeac6ddcf6cf64d5b7f392d8a1a2bdd5bd7`.

This is a new release after the preserved first source-audit failure in
27f83b98fa. That history, all four unchanged relocated source outputs and
all original external receipts/logs remain. No failed check is relabeled
as a pass. Distinct r2 receipt names prevent replacement of old evidence.

Run from the repository root, strictly in this order, with complete stdout
and stderr externally beside each JSON using the same stem plus `.stdout`
and `.stderr`. Stop every dependent operation at the first command/tool
failure. No silent edit, retry or continuation is allowed; a substantive
repair requires re-freezing and fresh full reviews before a new release.

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --output /tmp/grouped66-r2-build.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --source-only --output /tmp/grouped66-r2-source-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --source-only --output /tmp/grouped66-r2-source-audit-optimized.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-r2-build-check.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/build.py --check --output /tmp/grouped66-r2-build-check-optimized.json
python -B Computability/DiophantineConsistency/tools/render_grouped66_page.py --render --output /tmp/grouped66-r2-render.json
python -B Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-r2-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-grouped66/FRONT_AUDIT.py --output /tmp/grouped66-r2-audit-optimized.json
python -B Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-r2-rerender.json
python -B -O Computability/DiophantineConsistency/tools/render_grouped66_page.py --check --output /tmp/grouped66-r2-rerender-optimized.json
```

Only the producer's four declared source outputs and the renderer's five
declared PDF/text/log/data outputs may be materialized. All existing files
and receipts must first satisfy the reviewed byte/target guards. No held
code, TeX, proof, seed, parent, maintained page or Lean file may change.
No optional variant, compiler/search/Lean work, final metadata or manifest
closure is released here. Inspect actual exits and full receipts before
claiming success; stop also if receipt/stdout equality or status is wrong.

After all ten pass, ROOT must separately release six fresh independent
normal/optimized source checks, full audits and pure rerenders, compare
all twelve complete JSON/stdout byte strings and snapshot all immutable
inputs. Two actual visual reviews and separately released final metadata
closure precede acceptance or promotion. This document claims no retry
success, actual page fit, measured gain or maintained equation.pdf update.
