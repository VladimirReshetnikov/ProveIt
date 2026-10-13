# Signed Primitive Annuli and Compressed Basis Certificates for Unknot Hierarchies

Research package for ProveIt, 12 October 2026. Prepared with ChatGPT for
Vladimir Reshetnikov.

**Result:** an exact signed primitive-family terminal on cyclic support
blocks of rank at most two, with authenticated native source transport and
independent certificate replay. Five existing normal-cut inputs change from
`INCONCLUSIVE` to `COMPLETE`; all five agree with independent Regina cuts.
This package does **not** establish a complete quasi-polynomial unknot
recognizer. The article states the remaining hypotheses precisely.

## Start here

- `article/signed_primitive_annuli.pdf` — comprehensive article, with proofs,
  native worked examples, complexity accounting, and twelve research questions.
- `article/signed_primitive_annuli.tex` — main editable LaTeX source.
- `integration.patch` — implementation and regression patch against the pinned
  repository revision below.
- `PROVENANCE.json` — source revision, changed-file hashes, environment, and claim scope.
- `MANIFEST.sha256` — hashes of every delivered file other than the manifest itself.
- `verify_package.py` — checks the manifest and the cross-links between measured
  code, fixtures, certificates, exploration records, and the delivered snapshot.

Repository: https://github.com/VladimirReshetnikov/ProveIt

Baseline revision: `e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39`

Inspected source areas include `Topology/UnknotRecognition`, its synthesis,
and `docs/incoming` at that revision. No external branch was modified.

## Mathematical contribution and limits

The implementation keeps the actual signed ordered annular words, transports
them through a geometrically proved core cancellation, and checks whether
**one** automorphism carries **all** incident annuli in a core to distinct
generator conjugacy classes. The classical primitive-loop theorem then gives
simultaneous geometric dual disks, relative to disk ports.

The article proves the following statements with explicit hypotheses:

1. Complete column-private cancellations transport signed passive curves in
   a shared grammar with `O(L + r + p + q)` productions. This is a structural
   grammar bound, not a linear bit-time bound.
2. A supplied powered Nielsen sequence can be evaluated by backward shared
   replay in polynomial encoded size, without expanding its word images.
3. In rank two, any automorphism lifting the inverse exponent-sum matrix of
   a unimodular pair decides simultaneous conjugate primitivity after exact
   cyclic reduction. This is a derived simultaneous consequence of classical
   rank-two free-group theory and existing compressed-word algorithms.
4. Conjugate primitive families descend to containing subgroups. Consequently,
   a multiword decomposed into cyclic support blocks of size at most two can
   be decided in deterministic polynomial time, uniformly in total rank.
5. If every pending core annulus belongs to the certified family, the
   primitive-annulus gluing gives an exact handlebody census. The terminal
   does not preserve an arbitrary marked boundary pattern for future stages.
6. A geometric Fibonacci family separates this signed criterion from the
   prior fixed unsigned singleton-cancellation criterion. It is not claimed
   as a compiled family of native normal-surface inputs.

Classical and prior ProveIt results are attributed explicitly. In particular,
this is not a new general primitive-element algorithm, a new general
compressed-word reduction algorithm, or a completion of Lackenby's hierarchy.
Refusal by the new terminal is not a negative knot or manifold certificate.

Lackenby's announced target is `2^{O((log n)^3)} = n^{O((log n)^2)}`. The
conditional global accounting in the article includes surface discovery,
marked geometry, repairs, discarded work, and terminal completeness; none
of those missing global bounds is inferred from the local benchmarks.

## Package contents

| Path | Contents |
|---|---|
| `article/` | Main TeX, included theorem and data tables, bibliography, PDF, and compiled bibliography |
| `figures/` | Scientific compression plot in PDF and PNG |
| `code/fast/` | Complete Python-source snapshot of patched `fast/`, plus the two required local fixture banks |
| `experiments/algebra/` | Independent literal Whitehead and forward-substitution audit, with its report |
| `experiments/exploration/original/` | Original discovery scripts, preserved byte for byte |
| `experiments/exploration/recorded/` | Frozen exploration logs and candidate records |
| `experiments/exploration/run_exploration.py` | Relocates historical path constants to rerun exploration in a full checkout |
| `results/` | Frozen native, algebraic, compression, regression, and implementation records |
| `results/certificates/` | Five full authenticated whole-cut certificates |
| `results/logs/` | Full and targeted regression logs, including historical setup failures |
| `benchmark_compression.py` | Four compressed benchmark families, independently replayed |
| `make_tables_figures.py` | Regenerates article tables and the scientific figure from frozen results |

The snapshot includes the baseline Python dependencies used by the optional
Regina adapter. It does not duplicate every large historical report or
synthesis fixture. Run the explicitly named focused tests below in the
snapshot. Use a full pinned checkout for the entire upstream suite.

## Reproduce the delivered result

All commands in this section start in the extracted package root. The code
was tested with Python 3.12.14. The native producer and certificate verifier
use Python's standard library. Additional packages used for the reported
checks are listed in `PROVENANCE.json`:

```bash
python -m pip install pytest==9.1.1 regina==7.4.1 matplotlib==3.10.8
```

Regina is optional unless `--regina` is selected; its Python distribution
version is 7.4.1 and its reported library version is 7.4. Matplotlib is
needed only to regenerate figures. The PDF is already built.

### 1. Check file and evidence integrity

```bash
python verify_package.py
```

This does not rerun mathematical computations or fetch any sources. It
checks all manifest entries, measured-code hashes, canonical certificate
hashes, fixture identity, and the main frozen evidence counts.

### 2. Run the eighteen new focused tests

```bash
PYTHONPATH=code/fast python -m pytest -q \
  code/fast/tests/test_cyclic_basis.py \
  code/fast/tests/test_signed_annulus_source.py \
  code/fast/tests/test_signed_annulus_integration.py
```

### 3. Reproduce all five native gains and the retained refusal

```bash
PYTHONPATH=code/fast python -m signed_annulus_research.reproduce \
  --output replay/native --regina
```

Omit `--regina` for source authentication and independent native replay
without the optional expanded-cut oracle. The exact triangulations and
normal coordinates are embedded; no normal-surface enumeration order is
assumed. The source-bank hash is additionally checked when the historical
report is present in a full repository checkout.

The expected positive cases are `finite_figureEight/vertex71` and
`finite_figureEight_interior/vertex134`, `/vertex136`, `/vertex205`, and
`/vertex290`. Each gives two genus-two handlebodies. The retained refusal
is `finite_figureEight/vertex98`, whose relevant annular word is `x^5 y^2`.
This is a census of chosen cuts in a nontrivial knot exterior, not an unknot
verdict about that knot.

### 4. Reproduce the independent algebra audit

```bash
mkdir -p replay
python experiments/algebra/audit_cyclic_basis.py \
  --fast-path code/fast --output replay/algebra_audit.json
```

The frozen run has 8,486 decision inputs, 1,284 accepted certificates,
396 supplied Nielsen sequences, and 4,008 literal forward comparisons
plus 4,008 inverse roundtrips. There were no discrepancies. The seed,
generation caps, discarded oversized literal generations, and mutation
results are recorded. This audit has its own literal reduction and
Whitehead oracle; it does not use the producer's determinant decision.

### 5. Reproduce compressed benchmarks

```bash
python benchmark_compression.py --fast-root code/fast \
  --output replay/compression.json --repeats 3
```

Use `--quick` for a smaller grid. The four families are Fibonacci pairs,
binary shears, independent rank-two blocks, and triangular signed transport.
The largest shear input has expanded total length `2^2048 + 2`; production
and independent verification operate on grammars. The triangular source
packets are algebraic tests and do not assert a geometric realization.

Timings are observations from a shared host, not a claimed uniform speed-up
factor. Grammar size and exact certificate replay are more reproducible.
The finite measurements do not prove asymptotic complexity.

### 6. Rebuild the article

The TeX source uses standard TeX Live packages, BibTeX, and latexmk. From the
package root:

```bash
python make_tables_figures.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error signed_primitive_annuli.tex
```

The generated data tables and vector figure are already included, so
`latexmk` alone is sufficient to rebuild the article. The included `.bbl`
also permits ordinary repeated `pdflatex` runs without fetching a bibliography.
Regenerating files can alter metadata and invalidate their delivered manifest
hashes; verify the unmodified package first. No external images or fonts are
downloaded during the build.

## Integrate the patch into ProveIt

From a clean checkout of the pinned revision, substitute the actual absolute
path of the extracted archive:

```bash
git apply --check /absolute/path/to/package/integration.patch
git apply /absolute/path/to/package/integration.patch
```

The patch adds six producer/checker modules, three new test modules, the
native fixture/reproduction directory, and opt-in wrapper support. It also
pins two existing historical-refusal assertions to `lower_forest='source'`.
Those assertions were already stale under the baseline adaptive default;
the preserved baseline comparison is in `results/baseline_stale_expectation.json`.

Public usage, running Python from `Topology/UnknotRecognition/fast` or with
that directory on `PYTHONPATH`:

```python
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

result = normal_cut_handlebodies(
    triangulation,
    coordinates,
    annulus_method='signed_rank_two',
    record_certificate=True,
)
if result['status'] == 'COMPLETE':
    assert verify_normal_cut_handlebodies(
        triangulation, coordinates, result['certificate'])
```

The default remains `annulus_method='counts'`. Both default `masks` and
`moments` boundary methods have been checked on all five new cases. The
ordinary signed certificate is v1; the four top-reduced cases use v2.
Unsupported discovery blocks and resource exhaustion remain inconclusive.

### Full repository regression

All 1,741 collected tests passed across the full run and the necessary
targeted rerun. The final full run reported 1,733 passes and 1,750 passing
subtests in 506.68 seconds, with no assertion failures. Eight tests were
blocked at setup by a transitive historical fixture omitted during sparse
checkout. Restoring its exact pinned bytes yielded eight passes in 0.99
seconds. This is not represented as one uninterrupted green invocation.

The full suite needs the original report/synthesis fixtures, including
`Topology/UnknotRecognition/synthesis/data/cocycle-reuse-audit.json`, and Git
commit `1aeabfa735c78a30b732405b101009d376d56f18` for an existing frozen-output
test. In a shallow checkout, fetch that exact commit if needed:

```bash
git fetch --depth=1 --filter=blob:none origin 1aeabfa735c78a30b732405b101009d376d56f18
cd Topology/UnknotRecognition/fast
python -m pytest -q
```

The initial full run's disk-exhaustion failures, stale assertions, and
historical dependency issue are also retained and explained in
`results/regression_audit.json`. No failed test or setup error was silently
discarded from the report.

## Rerun the exploratory search

Exploration requires the **full** checkout, its report 57 discovery bank,
and Regina. For example, from the extracted package root:

```bash
python experiments/exploration/run_exploration.py discovery \
  --fast-root /absolute/path/to/ProveIt/Topology/UnknotRecognition/fast \
  --output replay/discovery
```

Other choices are `fibonacci`, `relabel`, and `inspect`. `--prepare-only`
relocates and syntax-checks the frozen scripts without running a search.
The runner changes only absolute path string constants; original scripts
and their hashes remain unchanged. Exploratory literal Whitehead search
is distinct from the compressed production terminal. Its elapsed time is
not a production benchmark.

The frozen discovery denominator is 1,374 stored standard vertex surfaces
excluding Fibonacci and connected-sum records: 1,205 baseline completions,
169 refusals, and five subsequently authenticated new signed successes.
Another 660 Fibonacci vertex/scaled cuts and 1,700 seed relabelings were
already complete under the baseline. These banks are reported separately
and are not pooled as independent random trials.

## Recommended next research milestones

The article develops twelve questions. The most immediate milestones are:

1. Construct compressed **marked** dual-disk data from a common basis
   certificate, suitable for the next hierarchy operation.
2. Characterize primitive families relative to additional annular ports.
3. Use homology normalization plus controlled IA corrections to handle
   larger support blocks, with a proved total certificate/search bound.
4. Extend signed transport to more general certified disk-slide schedules.
5. Prove constructive multisurface selection, region operations, repair
   amortization, and complete marked-terminal bounds that fit the global
   `2^{O((log n)^3)}` accounting.

The license is the repository's MIT No Attribution license in `LICENSE`.
