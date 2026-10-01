# Positivity at the First Feedback Boundary in Thue Morse Pressure

This report proves, for every integer m>=2:

- H_(m,m)=[a^(2m)]h_a(1/2)>0
- [t^(4m)]p_m(t/pi)>0

Together with the previous triangle theorem, both response and pressure
coefficients are now positive throughout 1<=r<=m. The response range cannot
uniformly extend one step: H_(2,3)=-488/27. Pressure at degree ten is still
positive, so response and pressure sharpness must be distinguished.

The proof has two explicit parts. A regularized orbit formula, strict tangent
comparison, and a Bernoulli mode bound prove every m>=70. Exact integer
reflection-block enclosures certify all 68 remaining moments m=2,...,69.
The report also proves a positive diagonal asymptotic for H_(m,m).

## Main files

- `article.pdf`: eight-page mathematical report
- `article.tex`: editable LaTeX source
- `code/run_all.py`: quick exact validation of the supplied certificates
- `code/reproduce_all.py`: full recomputation of all 68 matrix enclosures and every saved trace entry
- `code/check_boundary_parity.cpp`: primary exact GMP enclosure generator
- `code/check_trace_coverage.py`: independent standard-library trace audit
- `code/verify_cutoff.py`: exact rational analytic-cutoff certificate
- `code/check_m 2_response.py`: exact cubic proof of the response counterexample
- `code/check_m 2_pressure.py`: independent exact pressure cubic certificate
- `code/fourier_reference.py`: optional independent SymPy response comparisons
- `code/recompute_first_negatives.py`: optional exact later-sign exploration
- `data/certificates/`: per-moment rational enclosures and compressed per-order traces
- `data/`: exact cutoff, sharpness, reference, and audit data
- `PROOF_STATUS.md`, `SOURCES.md`, `VISUAL_QA.md`: scope, provenance, and inspection records
- `SHA 256SUMS.txt`: file-integrity manifest

## Verify

The quick check requires only Python 3:

    python 3 code/run_all.py

It validates all 68 saved traces, all 4828 scalar error recurrences, the baseline
vectors, final intervals, available exact comparisons, the rational analytic
cutoff, and the two cubic certificates. The audited generator itself checks
matrix inverse identities and every outward rounding operation.

For the complete matrix-level replay, use Python 3, a C++17 compiler, and GMP
with its C++ development headers and libraries:

    python 3 code/reproduce_all.py

This compiles the included source locally, recomputes all 68 enclosures using
two processes, and compares every trace entry to the supplied certificates.
Every arithmetic decision is exact integer arithmetic. The reported runtime
is metadata only. No floating-point estimate enters a sign certificate.

Optional reference calculations require SymPy 1.14.0:

    python 3 code/fourier_reference.py
    python 3 code/recompute_first_negatives.py

The latter regenerates the first negative pressure degree above 2m for m=2,...,14.
It is exploratory finite orientation, not a claimed general formula.

## Build

A normal TeX installation can run `pdflatex article.tex` twice.
`build_local.sh` reproduces the restricted-environment build without changing
a system TeX tree. Build and replay outputs go under `build/`.

The results are ordinary mathematics with a finite computer-assisted proof
component, independently reviewed but unrefereed and not verified in Lean.
The source ZIP is approximately 45MB because it preserves every per-order
integer vector and error bound. Earlier delivered reports remain unchanged.
