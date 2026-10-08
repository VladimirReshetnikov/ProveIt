"""Build and verify the repository integration ZIP without changing Git's index.

First build article.pdf. Then run:
  python3 build_release.py --output-dir /path/to/deliverables

The output contains only this continuation's overlay, not the full baseline.
The pinned Git object and an ordinary working checkout are required.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[3]
PROJECT = 'Topology/UnknotRecognition'
BASELINE = '58ee11a97d5fd7f21647c57eefaf3ecc007931d6'
NAME = 'ProveIt_Unknot_Quotient_Kernels_20261008'

FILES = [
    'fast/fastunknot/normal_surface.py',
    'fast/fastunknot/relator_overlap.py',
    'fast/fastunknot/scalar_split.py',
    'fast/fastunknot/coefficient_span.py',
    'fast/fastunknot/cyclic_overlap_index.py',
    'fast/fastunknot/interval_orbits.py',
    'fast/fastunknot/normal_surface_orbits.py',
    'fast/tests/test_normal_surface.py',
    'fast/tests/test_coefficient_span.py',
    'fast/tests/test_cyclic_overlap_index.py',
    'fast/tests/test_interval_orbits.py',
    'fast/tests/test_normal_surface_orbits.py',
    'fast/benchmark_coefficient_span.py',
]
DIRECTORIES = [
    'fast/coefficient_research', 'fast/cyclic_overlap_research',
    'fast/interval_research', 'fast/normal_orbit_research',
    'research/20261008_quotient_kernels',
]

VERIFY_SCRIPT = '''"""Verify every archived file against MANIFEST.sha256."""
from hashlib import sha256
from pathlib import Path
import sys

root = Path(__file__).resolve().parent
failures, checked = [], 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise SystemExit('Unsafe manifest path: ' + name)
    path = root / relative
    actual = sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if actual != expected:
        failures.append(name)
    checked += 1
if failures:
    print('Checksum failures:', *failures, sep='\\n')
    sys.exit(1)
print('Verified', checked, 'files; all SHA-256 checksums match.')
'''

README = '''# Exact Quotient Kernels for Unknot Recognition

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
'''


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def run(arguments, *, cwd=REPOSITORY, env=None, check=True):
    result = subprocess.run(arguments, cwd=cwd, env=env, capture_output=True)
    if check and result.returncode:
        raise RuntimeError('Command failed: ' + repr(arguments) + '\n' +
                           result.stderr.decode(errors='replace'))
    return result


def selected_files():
    chosen = {REPOSITORY / PROJECT / name for name in FILES}
    for directory in DIRECTORIES:
        chosen.update(p for p in (REPOSITORY / PROJECT / directory).rglob('*') if p.is_file())
    excluded_suffixes = {'.aux', '.out', '.toc', '.fls', '.fdb_latexmk', '.pyc'}
    result = []
    for path in sorted(chosen):
        if '__pycache__' in path.parts or path.suffix in excluded_suffixes:
            continue
        if path.parent == HERE and path.name in ('article.log', 'article.synctex.gz'):
            continue
        if path.is_symlink():
            raise ValueError('Refusing to package a symlink: ' + str(path))
        if not path.is_file():
            raise FileNotFoundError(path)
        result.append(path.relative_to(REPOSITORY).as_posix())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if output.is_relative_to(HERE):
        parser.error('Choose an output directory outside the article tree.')
    output.mkdir(parents=True, exist_ok=True)
    if run(['git', 'rev-parse', BASELINE]).stdout.decode().strip() != BASELINE:
        raise RuntimeError('Pinned baseline is unavailable.')
    files = selected_files()
    if not (HERE / 'article.pdf').is_file():
        raise FileNotFoundError('Build article.pdf first.')

    stage_parent = Path(tempfile.mkdtemp(prefix='proveit-release-', dir=output))
    stage = stage_parent / NAME
    stage.mkdir()
    overlay = stage / 'repo_overlay'
    for name in files:
        target = overlay / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPOSITORY / name, target)
    shutil.copy2(HERE / 'article.pdf', stage / 'article.pdf')
    (stage / 'LICENSE').write_bytes(run(['git', 'show', BASELINE + ':LICENSE']).stdout)
    (stage / 'README.md').write_text(README)
    (stage / 'verify_package.py').write_text(VERIFY_SCRIPT)

    with tempfile.TemporaryDirectory(prefix='proveit-index-') as temporary:
        env = os.environ.copy()
        env['GIT_INDEX_FILE'] = str(Path(temporary) / 'index')
        run(['git', 'read-tree', BASELINE], env=env)
        run(['git', 'add', '--sparse', '-f', '--', *files], env=env)
        patch = run(['git', 'diff', '--cached', '--binary', '--full-index',
                     '--no-ext-diff', '--src-prefix=a/', '--dst-prefix=b/',
                     BASELINE, '--', *files], env=env).stdout
    (stage / 'integration.patch').write_bytes(patch)

    inherited = []
    with tempfile.TemporaryDirectory(prefix='proveit-apply-') as temporary:
        clean = Path(temporary)
        for name in files:
            original = run(['git', 'show', BASELINE + ':' + name], check=False)
            if original.returncode == 0:
                destination = clean / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(original.stdout)
                inherited.append(name)
        run(['git', 'apply', '--check', str(stage / 'integration.patch')], cwd=clean)
        run(['git', 'apply', str(stage / 'integration.patch')], cwd=clean)
        comparisons = []
        for name in files:
            expected, actual = digest(overlay / name), digest(clean / name)
            if actual != expected:
                raise ArithmeticError('Patch output differs: ' + name)
            comparisons.append({'path': name, 'sha256': actual, 'matches': True})
    verification = {'baseline': BASELINE, 'apply_check': 'PASS', 'apply': 'PASS',
        'overlay_files': len(files), 'inherited_paths': inherited,
        'all_resulting_bytes_match': True, 'comparisons': comparisons,
        'scope': 'Clean reconstruction of all affected pinned files; full integration tests are recorded separately.'}
    (stage / 'patch_validation.json').write_text(json.dumps(verification, indent=2) + '\n')
    manifest = {'schema': 'proveit_quotient_kernels_release_v1', 'baseline': BASELINE,
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'package': NAME, 'overlay_files': len(files),
        'overlay_bytes': sum((overlay / name).stat().st_size for name in files),
        'article_sha256': digest(stage / 'article.pdf'),
        'patch_sha256': digest(stage / 'integration.patch'),
        'full_test_gate': {'tests': 807, 'failures': 0, 'errors': 0, 'skips': 0},
        'mathematical_status': 'Exact local results; global quasi-polynomial bound remains unproved.'}
    (stage / 'release_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    checksums = [f'{digest(path)}  {path.relative_to(stage).as_posix()}'
                 for path in sorted(stage.rglob('*')) if path.is_file()]
    (stage / 'MANIFEST.sha256').write_text('\n'.join(checksums) + '\n')
    verification_run = run(['python3', str(stage / 'verify_package.py')], cwd=stage)

    archive = output / (NAME + '.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for path in sorted(stage.rglob('*')):
            if path.is_file():
                zipped.write(path, (Path(NAME) / path.relative_to(stage)).as_posix())
    with zipfile.ZipFile(archive) as zipped:
        if zipped.testzip() is not None:
            raise ArithmeticError('ZIP integrity check failed.')
    pdf = output / (NAME + '.pdf')
    shutil.copy2(stage / 'article.pdf', pdf)
    print(json.dumps({'archive': str(archive), 'pdf': str(pdf), 'stage': str(stage),
        'zip_bytes': archive.stat().st_size, 'zip_sha256': digest(archive),
        'overlay_files': len(files), 'patch_bytes': len(patch),
        'verification': verification_run.stdout.decode().strip()}, indent=2))


if __name__ == '__main__':
    main()
