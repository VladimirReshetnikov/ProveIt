# Planar minimum subdivisions for complete normal-surface sectors

This package continues the ProveIt unknot-recognition research at commit
`8188525b70033dcfe7c51ea5ae2c8723ad0c0198`. It supplies exact enumeration of
all **non-link standard extreme rays in a supplied compatible sector whose
quadrilateral matching kernel has dimension at most three**. The projective
quadrilateral section may be a polygon, segment, point, or empty.

The accompanying article proves the correspondence with vertices of the
common minimum subdivision, an explicit quadratic output bound, a stronger
linear bound when only one vertex group varies, and polynomial local bit
complexity. It treats coincident forms, inactive ties, overlapping segments,
and lower feasible dimension. The result is a local component of the
quasi-polynomial research program; it does not establish a global
quasi-polynomial unknot recognizer.

## Contents

| Path | Purpose |
| --- | --- |
| [article/planar_sector_overlays.tex](article/planar_sector_overlays.tex) | Comprehensive research article, proofs, source attribution, and research questions |
| [article/planar_sector_overlays.pdf](article/planar_sector_overlays.pdf) | Compiled article |
| [code/](code/) | Complete pinned `fastunknot` runtime with the five additive files and three relevant test modules |
| [integration.patch](integration.patch) | Repository patch adding exactly three modules and two test files |
| [PROVENANCE.json](PROVENANCE.json) | Repository pin, all snapshot hashes, patch checks, environment, and evidence boundaries |
| [experiments/](experiments/) | Exact corpus audit, two independent adversarial audits, and paired benchmark |
| [fixtures/discovery_corpus.json](fixtures/discovery_corpus.json) | Frozen triangulations and full Regina reference enumerations |
| [results/](results/) | Original machine-readable observations and complete logs |
| [reproduce.py](reproduce.py) | Portable test and audit runner that preserves original evidence |
| [checksums.sha256](checksums.sha256) | SHA-256 digest of each delivered file other than the manifest itself |

The runtime snapshot contains every tracked file under the pinned
`Topology/UnknotRecognition/fast/fastunknot` package, unchanged except that
the three new modules are added. It also contains the baseline
`test_normal_sector_integration.py`, the two new test modules, the original
`pyproject.toml`, and the MIT-0 licenses. The standalone snapshot includes
30 relevant tests; the full maintained test suite is available in the
repository.

## Quick reproduction

Use Python 3.10 or later; this delivery was tested with Python 3.12.14. The
core algorithm and quick verification need only the standard library.

From the extracted package directory, run:

```sh
python reproduce.py --quick
```

Running `python reproduce.py` does the same thing. The quick workflow runs:

- 22 new geometry and certificate tests.
- Eight inherited supplied-sector integration tests.
- An independently written equality-arrangement and active-rank audit:
  304 exact models, 609 compared rays, and 1,409 feasible arrangement
  candidates, including polygon, segment, point, and empty sections.
- 96 focused certificate, integer-lift, malformed-input, source-binding,
  exact-budget, and cancellation assertions.
- The exact Euler-corner comparison on 607 declared sectors, checking
  equality of normalized maxima and membership of every corner lift in
  the complete frozen standard-ray list.

Each invocation creates a new uniquely named directory under
`results/reproduction/`. Its `summary.json` records source hashes, commands,
exit codes, and elapsed times; complete subprocess logs and new audit JSON
files are placed alongside it. Original experiment records remain intact.

The runner checks all bundled source hashes against `PROVENANCE.json`.
For testing an independently modified checkout, specify the directory that
contains `fastunknot` and `tests`:

```sh
python reproduce.py --quick --fast /path/to/ProveIt/Topology/UnknotRecognition/fast
```

An external checkout is recorded by its source hashes; its byte identity
with the pinned snapshot is not asserted.

### Individual checks

These commands reproduce the separate audits and put fresh evidence
in a separate directory:

```sh
python experiments/audit_abstract.py --output results/reproduction/manual_abstract.json
python experiments/audit_certificates.py --output results/reproduction/manual_certificates.json
python experiments/audit_euler_corners.py --output results/reproduction/manual_euler.json
```

The audit programs accept `--fast PATH` and default to the bundled
`code/` directory. To run just the new unit tests, enter `code/` and use:

```sh
python -B -S -m unittest discover -s tests -p 'test_sector_planar*.py' -v
```

The `-S` option demonstrates that this path does not require installed
third-party packages. The `-B` option avoids writing bytecode into the
snapshot.

## Full declared-corpus audit

The declared corpus audit compares all selected eligible sectors with the
frozen complete standard-ray lists:

```sh
python reproduce.py --full-audit
```

The original run selected 9,995 sectors and audited all 9,807 with matching
nullity at most three, including 463 nullity-three sectors. The 188 sectors
of greater nullity are outside this implementation's domain. The original
run also completed 607 independent ray-list replays and rejected 328 altered
enumeration certificates. See
[results/corpus_audit.json](results/corpus_audit.json) for the exact selection,
per-source results, and counts.

For fresh independent Regina enumerations, first install the optional
pinned dependency and then request the additional checks:

```sh
python -m pip install -r requirements.txt
python reproduce.py --full-audit --fresh-regina
```

Only this fresh-enumeration option needs Regina. The tested Python
distribution is Regina 7.4.1, which reports library version 7.4. The original
fresh run checked all 48 corpus sources and 36 additional double-cap family
examples. The corpus is deliberately assembled and is not a random sample
of knots or triangulations.

## Optional benchmark reproduction

Run the paired benchmark separately when the host is otherwise idle:

```sh
python reproduce.py --benchmark
```

This also runs the quick checks, then the declared paired experiment and
the new-only capacity rows. It uses the original audit record to reproduce
benchmark case selection. The benchmark records every warmup, measured
sample, configured deadline, source hash, and canonical ray digest.

The two protocols measure enumeration with an already-built kernel and
full kernel construction plus enumeration. Independent coverage replay,
fixture construction, digest calculation, and output serialization are
outside the paired timed calls. Every completed baseline/planar pair must
produce the same complete ray list. The reported ratios are medians of
within-round ratios. A second identical-planar arm measures host variability.

The original evidence includes 23 cases, 216 complete baseline/planar pairs,
and 222 identical-planar control pairs. It retains the empty-sector
regression and two capped baseline warmups. No speedup is assigned to a
capped comparison. Capacity rows have no baseline comparison; the largest
producer completed, while its separate independent replay reached the
declared allowance. Those are distinct outcomes. These experiments measure
supplied-sector enumeration, not end-to-end recognition.

See [results/paired_benchmark.json](results/paired_benchmark.json) for the full
evidence and the article for interpretation. The benchmark driver accepts
additional options; use `python experiments/benchmark.py --help`.

## Article and figure reproduction

The compiled article is self-contained for reading. Its TeX source uses
`validation_details.tex`, `benchmark_details.tex`,
`euler_corner_reduction.tex`, `euler_audit_details.tex`, and the included vector
figures in `article/figures/`. Build it with a standard TeX Live installation:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error planar_sector_overlays.tex
```

To regenerate the exact rational illustration, timing plots, and benchmark
fragment from the retained JSON, run from the package root:

```sh
python -m pip install -r requirements-article.txt
python experiments/make_article_assets.py
```

The figures were generated with Matplotlib 3.10.8 using the Agg backend.
The minimum-subdivision figure has exact rational data in
`article/figures/minimum_overlay_data.json`: its two strip families have
three and four cells, and their overlay has 12 cells and 20 vertices.
The timing figure shows actual replicate ranges and omits a completed
baseline point where the recorded warmup was capped.

The article additionally proves an Euler-only precheck using the original
quadrilateral corners, with post-kernel arithmetic cost `O(1+t+k²)`. It
uses convexity of canonical Euler characteristic and does not require a
complete minimum overlay. This precheck is examined by a separate exact
audit but is not integrated into the delivered runtime or certificate APIs.
A negative Euler result excludes an essential normal disc in the supplied
sector; a positive result still needs the topological essentiality observer.

The article also proves an effective-dimension extension and a one-LP
maximal-support extraction with independently checkable primal/dual
witnesses. This preprocessing is proposed and proved, but not implemented
in the delivered runtime. The implementation's admission gate remains raw
matching nullity at most three.

## Public interfaces and exact certificates

The three new runtime modules are:

- `fastunknot/sector_planar.py`: exact projective sections, minimum cells,
  subdivision overlay, primitive canonical lifting, counters, and limits.
- `fastunknot/sector_planar_verify.py`: independent dense elimination,
  a different chart, minimum-tie interval reconstruction, and complete-list
  checking.
- `fastunknot/sector_planar_certificate.py`: complete enumeration
  certificates and supplied-sector essential-disc queries.

For example, from the package directory:

```python
import sys
sys.path.insert(0, "code")

from fastunknot.sector_planar_certificate import certify_planar_sector
from fastunknot.sector_planar_verify import verify_planar_sector_certificate

solid_torus = {"tetrahedra": [[
    {"tetrahedron": 0, "permutation": [1, 2, 3, 0]},
    {"tetrahedron": 0, "permutation": [3, 0, 1, 2]},
    None, None,
]]}

result = certify_planar_sector(solid_torus, [(0, 2)], max_work=100000)
assert result["status"] == "COMPLETE"
assert verify_planar_sector_certificate(solid_torus, result["certificate"])
print(result["coordinates"])
```

The supplied triangulation is validated as a finite triangulation; the
sector permits at most one quadrilateral type per tetrahedron. Raw matching
nullity above three is rejected. Pure vertex links are omitted.

The enumeration schema `normal-sector-planar-rays-v1` binds the exact source
encoding, sorted compatible type list, and complete sorted primitive
quadrilateral ray list. The checker independently reconstructs that list;
it does not trust the producer's chart, winning labels, or traversal log.
It shares the native triangulation parser and the older dense matching
model, a dependency boundary documented in the article.

`discover_planar_in_sector` filters the complete primitive standard rays by
Euler characteristic and applies the established compressed essential-disc
observer. A positive result uses `normal-sector-witness-v1`. Restricted
negative results use `normal-sector-planar-exhaustion-v1`, with enumeration
coverage and every necessary negative component certificate. A negative
sector result does not identify all sectors of a manifold, and the source
hash does not prove that the supplied triangulation represents a particular
input knot diagram.

`max_work` bounds disclosed implementation checkpoints. Whole-query
producer wrappers share it across kernel construction, projective geometry,
and lifting. Component queries have their separate `max_orbit_cycles`
allowance; the independent verifier's allowance covers its reconstruction
geometry. A limit produces an interruption or `INCONCLUSIVE`, without a
partial list being labelled complete. Caller cancellation propagates.

## Repository integration

The additive patch contains exactly:

```text
Topology/UnknotRecognition/fast/fastunknot/sector_planar.py
Topology/UnknotRecognition/fast/fastunknot/sector_planar_verify.py
Topology/UnknotRecognition/fast/fastunknot/sector_planar_certificate.py
Topology/UnknotRecognition/fast/tests/test_sector_planar.py
Topology/UnknotRecognition/fast/tests/test_sector_planar_certificates.py
```

From a compatible ProveIt checkout, check and apply the patch:

```sh
git apply --check /path/to/unknot_planar_sector_overlays_20261009/integration.patch
git apply /path/to/unknot_planar_sector_overlays_20261009/integration.patch
```

The patch was applied to an isolated tree extracted from the pinned commit.
All five added files were compared byte for byte with the delivered source,
and every pre-existing file hash was preserved. The detailed result is
[results/patch_validation.json](results/patch_validation.json).

The new APIs are opt-in. Existing files, the default recognizer, and
dispatcher policy are unchanged. Integrate the article and experiment
artifacts according to the repository's incoming-report conventions; the
code patch intentionally contains only the five new implementation/test
files.

The full maintained checkout passed **1,344 tests**: 1,322 inherited tests
plus 22 new tests, in the recorded run of 155.470 seconds. Its original log
is [results/full_tests.log](results/full_tests.log). The quick bundled
workflow runs the relevant 30 tests and audits, not that entire maintained
suite.

## Rebuild the archive

After any intentional edits, rebuild the article and run the relevant
checks. Then regenerate the checksum manifest and deterministic ZIP:

```sh
python experiments/package_release.py
```

The archive is written one directory above the extracted package. The
builder uses a fixed entry order and timestamp, verifies every archived
file against the manifest, and checks all ZIP CRCs. Python bytecode and
TeX build auxiliaries are excluded. Original measured timeouts, adverse
controls, source records, and complete test logs remain in the evidence.

## Provenance and further work

[PROVENANCE.json](PROVENANCE.json) identifies each snapshot file as inherited
or new, records exact hashes and the verified patch boundary, and states the
algorithm's scope. Historical audit records keep the hashes present when
they ran. An early certificate wrapper was corrected to charge kernel
preparation to its whole-query allowance; final tests cover that boundary.
Later portable replays use the final source and checker documentation.
The final full-corpus replay at
`results/reproduction/final_corpus_audit.json` again completed every eligible
sector and all fresh Regina comparisons. Reproduction outputs record their own sources and never replace
the historical results automatically.

The article separates proven local results from the missing global bridge.
The main next questions concern complete discovery of useful low-nullity
sectors, controlled transitions between sectors, higher-dimensional
subdivisions, compact independent coverage proofs, and connecting the
geometric primitive to compressed hierarchy operations. None is assumed
resolved by the successful local tests or timings.

