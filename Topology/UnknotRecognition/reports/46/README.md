# Exact Quotient Kernels for Unknot Recognition

Research continuation for VladimirReshetnikov/ProveIt, 8 October 2026.

**Read `article.pdf` for the complete report.** The accompanying TeX,
figures, implementations, tests, raw measurements and provenance are under
`repo_overlay/Topology/UnknotRecognition/` at their intended repository paths.

The work supplies three exact local improvements and measured whole-query
Gordian acceleration. A general quasi-polynomial bound remains unproved;
the article states the missing hypotheses and twelve research questions.

## Integrate

Pinned baseline: `58ee11a97d5fd7f21647c57eefaf3ecc007931d6`.

The binary-capable patch includes every overlay file: production changes,
tests, benchmarks, raw data, article source, figures and PDF. Apply it once
from the root of a clean checkout containing the pinned baseline:

```bash
git apply --check /absolute/path/to/this/package/integration.patch
git apply /absolute/path/to/this/package/integration.patch
```

The patch was applied to a clean reconstruction of all affected baseline
files and the resulting bytes were compared with every overlay file.
`patch_validation.json` records that verification. `repo_overlay/` provides
the same complete files for inspection or manual integration; it is not a
standalone copy of the inherited project. Do not apply the patch twice.

## Main results and defaults

- The native AHT kernel uses the exact Fine–Wilf overlap threshold
  `p + q - gcd(p,q)` and supports signed counts and membership queries.
- The normal adapter computes component counts, orientability, boundary
  curves and Euler characteristic directly from binary coordinates in its
  supported finite torus-boundary triangulations. It does not certify the
  triangulation's correspondence with an input knot diagram.
- Coefficient-span and forest modes reconstruct the same full canonical
  scalar commutant. `direct` stays the default because the measured raw knot
  scans show no consistent complete-scan benefit.
- Explicit cyclic-overlap search now defaults to the bounded adaptive
  method, retaining `pairwise` and `joint` as audit options. Certificate
  format and both independent replayers are unchanged.
- The inherited normal-worker input deadlock and two scalar-space shortcut
  edge cases are repaired and documented separately from timing claims.

The full maintained suite passes **807 test methods**, with no errors,
failures or skips. A faithful baseline run has 768 methods with exactly one
inherited subprocess error. The raw whole-query study contains 760 completed
measured queries and 152 excluded warmups across 19 actual diagrams. Negative
and calibration results remain in the archive.

## Verify and reproduce

```bash
python3 verify_package.py
```

After integration, from `Topology/UnknotRecognition/fast`:

```bash
PYTHONPATH=. python3 -B -m unittest discover -s tests -v
```

The full suite needs the inherited `reports/24/reference`,
`reports/26/detshadow` and `reports/28/src/closure_reset` directories; restore
them if your checkout is sparse. The reported independent geometry checks
used Regina engine 7.4 (Python distribution 7.4.1).

The article directory's README gives all four benchmark commands, figure
generation, the source-digest audit and the LaTeX build command. Source data
are kept next to their benchmark scripts under `fast/*_research/`.

## Contents

| Path | Contents |
|---|---|
| `article.pdf` | Complete article |
| `integration.patch` | Verified Git patch for every overlay file |
| `repo_overlay/` | Repository-relative implementations, article, data and tests |
| `release_manifest.json` | Baseline, file count, sizes and release metadata |
| `patch_validation.json` | Patch application and byte-equality evidence |
| `MANIFEST.sha256` | SHA-256 digest of every other packaged file |
| `verify_package.py` | Portable checksum verifier |
| `LICENSE` | ProveIt baseline MIT No Attribution license |

The report's `PROVENANCE.md`, `source_hash_audit.json`,
`research_environment.json` and `validation/` distinguish inherited code,
classical theorems, new implementations, observed performance and open work.
No third-party orbit implementation or Regina binary is bundled.
