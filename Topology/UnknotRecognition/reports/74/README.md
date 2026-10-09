# Minimum envelopes for normal-surface sectors

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

**The main result is an exact, independently checkable enumeration of all
nonlink standard normal-surface rays in a supplied quadrilateral sector whose
matching kernel has dimension at most two.** The implementation uses the
actual minimum changes of the triangle potentials. It avoids the previous
enumeration of every pairwise potential equality and the subsequent rank
tests on spurious candidates.

Read [article/minimum_envelopes.pdf](article/minimum_envelopes.pdf) for the
complete article, or [article/minimum_envelopes.tex](article/minimum_envelopes.tex)
for its editable source. The package includes the proofs, experimental data,
independent certificates, implementation, integration patch, and proposed
research questions.

## Mathematical scope

The exact minimum-cell correspondence holds in every dimension. In matching
nullity two, normalization by the sum of the quadrilateral coordinates gives
an empty set, a point, or an interval. Its endpoints and the genuine changes
of each vertex's minimum potential give exactly the nonlink standard rays.
The paper proves the output bound

\[
R\le p-g+2\le a-k+4\le3k+4,
\]

for the nondegenerate interval case. Here `k` is the number of allowed
quadrilateral types, `p` is the retained triangle-class count, `g` is the
number of retained vertex groups, and `a <= 4k` counts nonzero-labelled
matching edges. Since `p` and the output count are both `O(k)`, the article
also proves an `O(tk)` post-kernel arithmetic bound for `1 <= k <= t`,
including full coordinate output. Kernel construction and native coordinate
validation are charged separately. The bit-time bound is polynomial; no
quadratic bit-time bound is claimed. The implementation reuses projected
affine potentials across all its output lifts.

An all-size capped Fibonacci solid-torus family makes the effect concrete.
The complete standard list has three rays, including an essential disc that
is absent from the quadrilateral-ray list. The old method considers `n + 2`
nonnegative directions and rejects `n - 1` of them. The paper also classifies
every integral surface in this two-parameter family by its components and
essential-disc count.

**This package does not establish quasi-polynomial complexity for unrestricted
unknot recognition.** The conditional global consequence still requires a
constructive, complete family of sufficiently few sectors, controlled
coordinate and transition costs, and the required binding to the original
knot diagram. Neither the number of sectors needed nor such a complete
search is proved here. The geometric APIs validate a supplied compact,
connected, orientable finite triangulation with one torus boundary; they do
not authenticate it as the exterior of an independently supplied diagram.

## Quick verification

With Python 3.12 (tested on 3.12.14), run from this package directory:

```sh
python reproduce.py
```

The default is a short, standard-library-only check. It verifies the recorded
source hashes and frozen-corpus bindings, replays all 60 saved eligible
certificates from the independent audit and all six coverage-benchmark
certificates, replays the extra essential-disc example, and runs all 24
focused tests. Enumeration-producer imports are blocked during saved-proof
replay. The six higher-nullity model-only audit records remain explicitly
outside the new enumeration API.

Every run creates a fresh directory under `reproduction/` containing its logs
and run report. The original `results/`, `fixtures/`, source snapshot and
article are preserved.

Optional workflows can be combined:

```sh
python reproduce.py --audit
python reproduce.py --fresh-regina
python reproduce.py --family
python reproduce.py --bench
python reproduce.py --pdf
```

`--audit` repeats the 9,344 eligible comparisons against the frozen full
standard-ray oracle. `--fresh-regina` implies that audit and additionally
repeats the 15 declared fresh Regina enumerations. `--family` checks the
closed formulas and topology counts. `--bench` repeats both complete timing
protocols: five paired rounds for enumeration and three paired rounds for
enumeration plus independent coverage checking. It takes several minutes
and should be run after other CPU-intensive work finishes. `--pdf` runs
pdfLaTeX twice, placing the rebuilt PDF and auxiliary files in that run's
reproduction directory.

Regina and figure-generation dependencies are optional and pinned in
`requirements-optional.txt`. The recorded Regina distribution was 7.4.1;
its own version string is 7.4. A system TeX installation is required only
for rebuilding the PDF.

## Recorded validation

| Evidence | Result |
|---|---:|
| Frozen triangulations | 48 |
| Declared selected sectors | 9,995 |
| Eligible sectors, nullity at most two | 9,344 |
| Emitted rays agreeing with the complete frozen oracle | 4,853 |
| Genuine interior minimum-fan rays | 804 |
| Fresh complete Regina enumerations | 15 |
| Independent audit certificates replayed | 60 |
| Coverage-benchmark certificates replayed | 6 |
| Final focused tests | 24 passing |

The larger retained repository test run passed **1,334 tests** before the
last three focused tests were added. A separate final run passed all **24
focused tests**. These groups overlap and should not be added together.
The package contains the focused suite and the full-run log; the entire
repository test suite is available in ProveIt after applying the patch.

The declared finite sector selection is detailed in
`code/sector_envelope_research/audit.py`. It includes all observed ray supports,
all supports of size at most two, and deterministic full-sector draws; for
at most three tetrahedra it includes every compatible support. It does not
exhaust every sector on the larger triangulations. The 651 selected sectors
with larger matching nullity are recorded and skipped.

## Performance results

These measurements concern complete enumeration in supplied sectors, with
the exact same output rays on both sides. The old source is pinned and
retained, fixture construction and final reporting serialization are outside
timed regions, warm-ups are retained separately, and every timed output has
a checked canonical ray hash. In the coverage protocol, the old arm's
ray-list equality check and the certificate replay/source-binding hashes
are inside the timed region; only final reporting hashes are outside it.

On the cap-type-1 Fibonacci family:

| Total tetrahedra | Measured operation | Old median | New median | Median paired speedup |
|---:|---|---:|---:|---:|
| 17 | Kernel build and complete enumeration | 476.595 ms | 6.921 ms | 68.859x |
| 33 | Kernel build and complete enumeration | 6,063.538 ms | 29.023 ms | 202.713x |
| 33 | Complete enumeration with a reused kernel | 6,592.798 ms | 8.204 ms | 781.169x |
| 17 | Production and independent coverage checking | 1,326.585 ms | 29.259 ms | 51.920x |

Paired medians are calculated from the individual within-round ratios; they
need not equal the ratio of the two separately reported medians. The
coverage comparison includes the former independent dense reconstruction of
the complete ray list on the old side and the compact coverage verifier on
the new side.

At 257 tetrahedra, the new-only full-build observation took 7.889 seconds,
with 7.493 seconds in kernel construction and 0.396 seconds in enumeration.
There is no old-arm measurement at that size. The recorded A/A controls show
visible host variability, so the report makes no tight timing-confidence
claim. These targeted family measurements are not measurements of a
complete knot recognizer and do not establish a uniform practical speedup
across all triangulations.

## Software and integration

The integration is **opt-in**. The existing `method='auto'` policy and
ordinary diagram-recognition schedule remain unchanged. Use
`method='envelope'` with `phase='standard'` on the sector API, or call
`certify_sector_enumeration` for a complete ray list with a portable coverage
certificate. Nullity above two is rejected explicitly.

`max_bases` counts begun output lifts in the envelope method. Exhaustion
raises `SearchLimit`; a partial iterator is not a completeness certificate.
The certificate-producing interface uses `max_rays`: exhaustion returns
`INCONCLUSIVE` without a partial completeness certificate. Limits do not
bound bit operations or replace the cooperative `check` callback.

See [INTEGRATION.md](INTEGRATION.md) for the exact patch scope, commands, API
examples and trust boundaries. The baseline commit is:

```text
66098968e88bba797143ac1bf7ad0ac4c5f697df
```

`code/` is a standalone reproduction snapshot containing the maintained
dependencies and the new code. It is not a full repository checkout.
`integration.patch` changes one existing maintained file and adds the three
new modules, two focused test files and six research files. It was checked
in an isolated checkout of the pinned revision, and every applied file was
byte-compared with the delivered snapshot. No original repository staging,
commit or push was performed.

The inherited MIT No Attribution license is supplied in `LICENSE`.

## Archive contents

| Path | Contents |
|---|---|
| `article/` | Complete LaTeX source, compiled PDF, included tables and figures |
| `code/` | Patched implementation snapshot, maintained dependencies, focused tests and research tools |
| `fixtures/` | Frozen finite-triangulation corpus with complete reference ray lists |
| `results/` | Exact audit records, raw timed calls, saved certificates, test logs and runtime metadata |
| `examples/` | The extra standard-ray essential-disc example and its replayable certificate |
| `experiments/` | Coverage benchmark, closed-form family oracle and figure/table generator |
| `reference/` | Exact predecessor of the modified sector module |
| `reproduction/` | Recorded standalone reproduction and patch-application checks |
| `integration.patch` | Reviewed change set against the pinned repository |
| `reproduce.py` | Quick verification and optional full reproduction workflows |
| `MANIFEST.sha256` | File-integrity checksums for the release contents |
