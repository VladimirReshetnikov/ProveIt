# Sparse-error minimal pairs and coarse representative spectra

Research report prepared for Vladimir Reshetnikov, 18 September 2026.

## Read first

`sparse_error_minimal_pairs.pdf` is the complete English proof report.
`sparse_error_minimal_pairs.tex` is its self-contained LaTeX source.

The selected target was C1 in the supplied `turing_degrees_unified.tex`:
whether every nonuniform coarse-equivalence class contains a representative
of least Turing degree. The source audit found that its negative coarse
answer is already implicit in earlier work. The report does not claim
priority for that answer or certify the novelty of the stronger results.

## Mathematical claims proved in the report

For a prescribed computable nondecreasing unbounded integer order h(n) <= n+1
and positive rational budget b, the report constructs individually 1-generic
sets A,B computable in the second Turing jump, forming a Turing minimal pair,
with

    sum_{n in A symmetric_difference B} 1/h(n) <= b.

Their disagreement count is o(h(N)), and their shared nonzero coarse class
has no least Turing-degree representative. Choosing an integer logarithmic
order yields o(log N) errors.

The report also proves a representative-spectrum identity and realizes each
Turing degree as an unattained infimum of a coarse representative spectrum.
These are mathematical proofs presented for independent checking, not claims
of peer review or machine-checked correctness. No conclusion is asserted for
effective-dense equivalence, and no claim is made that the spectra have no
minimal elements.

## Files

- `sparse_error_minimal_pairs.tex`: main source, bibliography included.
- `sparse_error_minimal_pairs.pdf`: compiled report.
- `finite_checks.py`: executable exact finite diagnostics (standard library).
- `finite_checks_results.json`: actual results from executing the checks.
- `source_audit.md`: source locations and status/novelty boundaries.
- `verification_notes.md`: proof-critical hypotheses and test limitations.
- `build.sh`: build the report in a separate work directory.

No font files, external research-paper PDFs, or LaTeX intermediate files are
redistributed.

## Reproduce the finite checks

Requires Python 3.10 or later. Run from this directory:

    python3 finite_checks.py --output finite_checks_results.json

The program exits unsuccessfully if an assertion fails. It uses exact
rational arithmetic, fixed random seeds for the finite arithmetic samples,
and exhaustive enumeration for the 65,536-labeling bridge test.

These tests do NOT compute the infinite A and B. They do NOT implement a
halting oracle, prove genericity, or verify Turing nonreducibility. The oracle
construction is specified transparently in Appendix A of the report. A
finite timeout is not a legitimate substitute for its negative decisions.

## Build the PDF

Install a LaTeX distribution with pdfLaTeX and the standard packages listed
in the preamble (including Latin Modern, AMS, microtype, hyperref, listings,
and titlesec). Then run:

    bash build.sh

No BibTeX run, internet access, proprietary fonts, or shell-escape is needed.
The source follows the Latin Modern / navy heading style of the attachment.

## Verification status

The English argument was internally audited; the Python diagnostics were
executed; the PDF was compiled and rendered for layout inspection. There is
no Lean formalization and no independent mathematical referee report.
