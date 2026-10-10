# Polylogarithms: Global Euler Extremizers, Polynomial Zero Thresholds, and Mixed Gaussian Identities

Research continuation for the ProveIt project, 10 October 2026.

The complete article is **article.pdf**. Its editable master is **article.tex**,
with proofs in **sections/** and bibliography in **references.tex**.

The source baseline is the immutable ProveIt revision
**4c173c06cc32c9cea554b39be1837ad2ae897fc1**, including all six archives then
present in docs/incoming. This package is a proposed contribution for review
and integration. It does not modify the source repository.

## Principal results

| Topic | Result | Status |
|---|---|---|
| Positive Euler kernel | Global maxima converge to a unique nondegenerate exponential-kernel maximum, approximately 1.0538619303627116; uniform enclosure and convergent extremizer expansion | Proved |
| Finite kernel extremum | Unique maximum at truncation two, characterized by a degree-seven polynomial; maximum approximately 1.1189386859610527 | Proved, with exact rational enclosures |
| Order-averaged Euler constant | Eventual exact reduction to the outer-order axis; conjectured decay exponent log(2)/log(3/2) and leading constant established | Proved |
| Next order scale | A threshold-layer correction with exponent approximately 1.96959041447, an optimizer displacement, and an exact near-maximizer criterion | Proved asymptotic statements |
| Reciprocal-gamma Appell roots | Minimum root spacing at least 1/(10 n²) | Proved for every n ≥ 2 |
| Lerch derivative zeros | Exactly n simple positive zeros whenever k ≥ ceil((16 + 240 n² H_(n−1))²), uniformly for 0 ≤ rho ≤ 1; log-location error less than 8/sqrt(k) | Proved |
| Negative outer orders | Exactly one simple inner-order sign transition at each of outer orders −2 and −3 | Proved |
| Mixed Gaussian generator | Exact shift equation, rational cyclotomic samples and parameter jets, integer values and pole finite parts, and convergent resummations | Proved |
| Weight-fifteen S14 reduction | Frozen primitive 16-term vector; normalized residual has absolute value below 10^−775 | Proximity proved; equality conjectural |

Eventual statements do **not** include a numerical starting index. The
all-finite-index kernel and order-extremizer questions remain open in the
specified ranges. S6, S8, S10, S12, and the new S14 equality remain conjectural.
S4 and the recorded golden weight-five evaluations were already proved in the
baseline and are not claimed as new here.

The article supplies full ordinary mathematical proofs, an audit and precise
status changes, and fourteen further research questions. It is an AI-assisted
research draft with reproducible artifacts, not an external referee report
or a proof-assistant formalization. Advancement is relative to the inspected
pinned source; no exhaustive literature-priority claim is made.

## Build the article

Run from this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error article.tex

Or:

    make pdf

If latexmk is unavailable, run pdfLaTeX repeatedly until references stabilize.
The document uses ordinary TeX Live mathematics, Latin Modern fonts,
microtype, placeins, and hyperref packages. The shipped figures are PDFs,
so rebuilding the article does not require Python.

## Replay the exact certificates

Python 3.11 or later is recommended. The default replay needs **only the
Python standard library**:

    python code/verify_all.py

It executes these four checks:

1. **verify_kernel.py**: rational logarithm and exponential intervals,
   unique-root endpoint brackets, the limiting constants, and the N=2
   stationary identities and value interval.
2. **verify_order_constants.py**: exact rational checks of twelve strict
   exponent comparisons used in the uniform asymptotic arguments.
3. **verify_mesh.py**: exact mesh-constant arithmetic, finite formula
   cross-checks, and the integer thresholds including their upward ceilings.
4. **verify_s14.py**: reconstruction from the frozen integer vector of every
   basket interval and both endpoints of the normalized residual interval.

The last calculation is the dominant step. It uses 2,600 exact Euler terms,
650 arctangent terms per Machin component, and 950 terms for log(2).
The delivered full replay took about 106 seconds in the recorded environment;
timings depend on the machine.

The replay report is written to **verification/replay_report.json**.
Failure produces a nonzero process exit code. Primary certificate checks use
unconditional validations rather than Python assertions that optimization
could disable.

The kernel, mesh and S14 verifiers compare the delivered records by default;
their **--write** options regenerate those records. The exponent verifier
recomputes and writes its exact record. Exact arithmetic still depends on the
stated analytic tail and uniqueness theorems: the programs are not themselves
formalizations of the full analysis.

## Run independent numerical and symbolic diagnostics

Install the optional packages used for this delivery:

    python -m pip install -r requirements.txt
    python code/verify_all.py --diagnostics

The exact checks run first. Diagnostics run only if all exact checks pass.
The optional stage includes:

| Program | Purpose |
|---|---|
| code/kernel_diagnostics.py | High-precision local stationary points and derivative coefficients; independent exact SymPy elimination; kernel figure |
| code/order_asymptotic_diagnostics.py | Threshold Mellin integral and asymptotic constants |
| code/verify_negative_orders.py | Exact rational kernels and root counts; independent Dirichlet and Mellin values |
| code/verify_mixed_generator.py | Rational samples, integer samples, pole finite parts, and the three resummations |
| code/audit_s14.py | Independent 110-digit Mellin audit of the frozen vector |

The scripts and data explicitly distinguish symbolic identities and exact
intervals from floating-point diagnostics. In particular, local numerical
stationary points do not certify global finite-index extrema.

The discovery calculation is optional and deliberately separate:

    python code/search_s14.py

Its output is evidence for a candidate, not an identity proof. The exact replay
does not rediscover the vector or depend on floating-point approximations to
the periods.

To regenerate all figures:

    make figures

## Organization

| Path | Contents |
|---|---|
| article.tex, article.pdf | Master TeX and reviewed PDF |
| sections/ | Abstract, complete proofs, audit, and research agenda |
| references.tex | Pinned source and primary mathematical references |
| code/ | Exact verifiers, diagnostics, figure sources, and package utilities |
| data/ | Frozen vector, rational certificates, and diagnostic records |
| figures/ | Standalone PDF and PNG figures |
| integration/INTEGRATION.md | Exact source labels and proposed placement |
| integration/proposed_status_updates.tex | Reviewable status insertion; not automatically applied |
| provenance/source_snapshot.json | Commit, tree, archive identities and SHA-256/Git-blob comparisons |
| provenance/runtime.json | Actual software and executable versions |
| verification/ | Replay and mathematical/PDF review records |
| MANIFEST.sha256 | Checksums of the delivered payload |
| LICENSE | ProveIt-compatible MIT No Attribution license |

For integration, begin with **integration/INTEGRATION.md**. It distinguishes
solved conjectures from partial progress and preserves the stronger finite
statements that remain open. The reusable TeX label prefixes are ker:, ord:,
mesh:, neg:, and mix:; macro and notation compatibility is documented.

## Integrity and repackaging

Check the delivered payload:

    python code/check_integrity.py

After rebuilding or intentionally changing the package, regenerate its manifest
and ZIP:

    python code/package_release.py

The ZIP is written beside this directory. Build auxiliaries and Python bytecode
are omitted. The manifest records the exact delivered files, so an intentional
local regeneration can change a checksum without indicating a mathematical
failure; use the certificate replay to test the mathematical data.

## Three readable exact identities

With

$$S_p=\sum_{n\ge0}\frac{(-1)^nH_n}{(2n+1)^p},$$

the article proves

$$\sum_{m\ge1}S_{2m}=\frac{\log^2 2}{4}-\frac{\pi^2}{48},$$

$$\sum_{m\ge1}2^{2m-1}S_{2m}=\log2-1,$$

and the pole-subtracted identity

$$\sum_{m\ge1}3^{2m-1}\left(S_{2m}+3^{-2m}\right)
=\log2-\frac{\log^2 2}{4}+\frac{\pi^2}{48}-\frac7{12}.$$

All three are convergent identities across weights. They do not, by
coefficient extraction alone, prove the individual fixed-weight conjectures.
