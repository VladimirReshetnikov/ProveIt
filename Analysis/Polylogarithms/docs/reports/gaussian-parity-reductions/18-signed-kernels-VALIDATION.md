# Validation record

Research snapshot: 9 October 2026.

## Executed mathematical and computational checks

`python code/verify.py` passed **588 check cases** at
400 Euler terms. The final recorded run took 21.591
seconds in this environment (Python 3.13.5, SymPy 1.14.0).
This is a run receipt, not a cross-platform performance benchmark.

All 64 even-weight formulas through weight 16 have independent rational
interval comparisons. The exact data inventory contains 64 reduction records,
64 corresponding interval records, and 15 exact odd-weight rank records.
The S4 discrepancy enclosure was checked, using `Fraction`, to be contained
in [-10^-118, 10^-118]. All delivered JSON files parse successfully.

`python code/numerics.py` passed its separate diagnostics: 16 Euler-error
cases, nine zero-asymptotic cases, nine illustrative zero-table entries, and
one S4 replay. mpmath version: 1.3.0; working precision: 120 decimal
digits. Recorded runtime: 3.069 seconds.

Both scripts refuse Python optimization mode (`-O`), so their assertions
cannot be silently disabled while reporting a successful verification run.

## Document build and inspection

The standalone article compiled with pdfLaTeX/latexmk to **23 A4 pages**.
The final LaTeX log has no overfull or underfull boxes, undefined references,
or LaTeX warnings. The PDF was rendered with Poppler and all pages reviewed
in contact sheets; representative proof, contents, table, and reference pages
were inspected individually. The appendix was moved to a fresh page to avoid
splitting its first identity across a page boundary. Final PDF text extraction
also confirms the verification count and the presence of the S4 bound.

The additive integration fragment and all 64 generated LaTeX formulas were
separately smoke-compiled with representative theorem environments and the
required packages, without layout or reference warnings. This is not a build
of the complete remote ProveIt manuscript.

## Trust boundary

The mathematical proofs are in the article. Exact algebra and interval checks
are complementary replay artifacts, not formal proof-assistant verification.
The article does not establish the S4 identity, the infinite rank conjecture,
period independence, or exhaustive novelty priority. The numerical root table
is not a certified root-isolation table.

The source repository was read through its connector and was not modified.
The delivered checksum manifest identifies the exact package snapshot; running
the generation scripts again changes receipts and may require a new manifest.
