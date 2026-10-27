# Adaptive aggregation for subexponential SAT

Research prepared for Vladimir Reshetnikov, October 26, 2026.

Start with **adaptive_sat_review.pdf**. Its complete source is
**adaptive_sat_review.tex**.

## Results

The source review covers fifteen refinement packets and two primary
manuscripts at ProveIt commit
`474ddba696a5d385c091c23fb2995f69edd13e00`, including all eight second-round packets. Seven arrived in
`3e57705cf14ee9ac99c0ac35cfff751dcf70b396`; the matching packet arrived in
`d098ba436b33df19365a44dd178694ff52845d19`. All eight were filed in
`6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a` during the closing check.

Under the reviewed normalized contraction interface, with `s` Boolean wires:

| New branch | Time exponent coefficient on `s/sqrt(log2 s)` | Space |
|---|---:|---|
| Streamed balanced recursive separators | 55.70947831890997 | Polynomial |
| Adaptive nine-group cached aggregation | 36.75031252383623 | Coefficient 34.02417800749051 on the same exponent scale |
| Adaptive cached aggregation, root degree at most `ceil(s^(1/12))` | 15.3919331988 | Coefficient 14.2501611298 on the same scale |

All coefficients mean `C+o(1)`, with polynomial factors as specified in the
report. Safe eventual coefficients are respectively **56**, **37/35**, and
**16/15**. They are wire-level certificates, not SAT-variable constants or
observed SAT runtimes.

The composed `r=16` polynomial-space reference combines the reviewed packing
and mode improvements and approaches their parameter boundary:
**66.19272369357722**. Streamed conditioning lowers this reference by the
factor `sqrt(17/24)` and also improves the preliminary two-alphabet retuning
**66.12052562523922**. No optimization over all possible schedules is claimed.
The generic conditioning technique is classical;
the new corpus contribution is its exact-weight mode-graph application and
the fully paid child-call/space analysis. The faster adaptive branch also
improves the stronger fixed-partition composition, rather than comparing only
with the much larger coefficients displayed by individual older packets.

The practical deliverable is an exact modular Cauchy feature kernel. On six
five-repeat paired synthetic fixtures, it is **6.22x–58.62x faster** than a
strengthened rational recurrence with the same mode cutoff. Every output is
equal. The product recurrence and mode weights are prior ingredients; bounded
modular arithmetic, safe valuation cancellation, denominator reuse and the
tested implementation supply the new practical improvement. Batch inversion
is optional and is not uniformly faster than separate cached inversions.

## Scope

The report proves the new aggregation identities and resource bounds, while
preserving explicit dependencies on the source deformation, precision,
packing, integral basis, child construction, and SAT reductions. There is no
new proof-assistant build or completed end-to-end SAT solver in this archive.
The general `n loglog(n)/sqrt(log(n))` SAT order is unchanged. The stronger
`n/log(n)`-type conditional targets remain unproved. The extra-memory and
low-degree branches must be compared under their own resource/premise limits.

The implemented arithmetic kernel supports integer-pair parameters in
`(Z/2^p Z)[U]/(U^2+U+1)`, including the scalar subring. It is not a generic
implementation of every unramified extension degree.

## Contents

- `adaptive_sat_review.tex`, `adaptive_sat_review.pdf`: full review, proofs,
  schedules, comparisons, measurements and limitations.
- `code/adaptive_blocks.py`: cached adaptive aggregation and generic streamed
  recursive conditioning for finite mode graphs.
- `code/modular_cauchy.py`: finite-precision feature tables and a streaming API.
- `code/reference_joint_cauchy.py`: unchanged archived source; its identity is
  recorded in `provenance/source_manifest.json`.
- `code/reference_recurrence.py`: stronger same-cutoff exact arithmetic control.
- `code/check_*.py`: exact algebra, independent reconstruction, call accounting,
  partition, capacity and schedule checks. Checks stay active under `python -O`.
- `code/benchmark_kernel.py`: paired benchmark with raw wall and CPU samples.
- `results/`: recorded correctness, benchmark and build results; the CSV is
  an exact tabular projection of the benchmark JSON.
- `audit/`: source-frontier audit, independent mathematical/code reviews,
  component proofs and implementation notes.
- `provenance/`: immutable source URLs, file/archive hashes and relevant commits.
- `run_checks.py`, `build_report.py`, `Makefile`, `verify_manifest.py`: local replay.
- `MANIFEST.sha256.json`: hashes of the delivered files, excluding itself.

## Reproduce

Use Python 3.10 or newer, standard library only, for all mathematical and
kernel checks. Verify the delivered bytes **before** regenerating outputs:

```bash
python3 verify_manifest.py
python3 run_checks.py
```

The replay runs the five checker programs in ordinary and optimized Python
and compares their deterministic outputs. It rewrites their result files.
It does not rerun benchmarks by default. To measure the current machine:

```bash
python3 code/benchmark_kernel.py --repeats 5 --output results/benchmark_rerun.json
```

Elapsed times can differ by environment; compare exact output digests and
paired local timings, not equality of old and new elapsed times.

To rebuild the PDF, install pdfLaTeX with the packages listed in the TeX
preamble, then run:

```bash
python3 build_report.py
```

The build uses three local passes with shell escape disabled and rejects
overfull boxes or undefined references. `_build/` is disposable. No source
repository script, network download, or upstream formalization is invoked.

## Verification evidence

- Primary kernel checker: 1,092 cases; 35,868 original-polynomial matrix
  reconstructions; 74,976 target/source comparisons; streaming, inversion,
  signed/zero/nonunit and invalid-input checks.
- Independent modular oracle: 63 additional cases through `N=128`, `p=129`;
  493 reconstructions plus 493 direct-entry checks and 27 full-table comparisons.
- Mode graph checker: 240 adaptive and 300 streamed comparisons with literal
  sums; all 280 partitions; 160 exact averaging cases; rational coefficient
  certificates.
- Independent recursive-conditioning implementation: 40 cases over the
  nonfield ring `(Z/64Z)[V]/(V^2)`, with individual oracle-call and live-context
  counts checked.
- Integer capacity/maximality, floor and large symbolic-margin checks.

All pass under normal Python and `python -O`. Finite checks validate these
components; the uniform asymptotic argument is the mathematical proof in the
report. Checksums record the delivered bytes and are not a signature.
