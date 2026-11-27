# Exact laws for arbitrary symplectic compressions

Research report, 26 November 2026.

## Main results

The report answers the general symplectic-compression question
spn:q:symplectic in the pinned ProveIt Article.

1. Exact probability of every compression between arbitrary source and
   target subspaces, allowing degenerate restricted alternating forms.
2. Exact support and minimum ambient symplectic dimension from three ranks.
3. Universal fixed-complement boundary discrepancy, independent of the
   fixed source form; rank-only discrepancy tends to zero exponentially.
4. Closed formulas and optimal tests for a symplectic-plane source.

These are unconditional finite-field results inspired by the finite-field
spanning component of the GRH proof. They do not assume RH or GRH.
The report establishes a new extension beyond the supplied Article.
Worldwide publication priority is not established; relevant classical
counting literature is discussed in the paper.

## Read and reproduce

Start with report.pdf. The editable source is report.tex and the four
section files in sections/. Build from this directory:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Python 3, standard library only:

    python3 code/compression_law.py
    python3 code/verify_counts.py --check-calculator --output results.json

The verifier uses exact arithmetic and independently enumerated symplectic
group elements. It checks every outcome in each selected case, including
forbidden matrices. results.json records coverage and outcomes. The main
run checked 125,232 matrix outcomes across 87 dimension/form cases.

## Calculator

code/compression_law.py supplies exact functions:

- qbin, general_linear_order, symplectic_order, frame_count
- transverse_count, compression_probability, compression_likelihood
- compression_invariants, compression_supported, plane_distances
- gram_map_count, alternating_form_count, gram_boundary_law,
  gram_boundary_delta

Read the function docstrings for exact argument order. Matrix operations
are implemented for prime fields only and reject nonprime moduli. The
mathematical theorems hold over every finite field. The scalar counting
formulas may be evaluated at prime powers without field elimination.
All probabilities and distances use Fraction; decimals in
example_results.json are displays of exact values.

## Source snapshots

- lsernau/grh-lean:
  72fead102f663d5c7a407964a13dc0cf9d977207
- VladimirReshetnikov/ProveIt:
  fc9889c80312959aee9893ab21bfc9e741719e88

provenance/ contains the detailed source manifest and focused analysis.
No GitHub repository was modified for this deliverable.

## Proof and validation status

The paper contains complete mathematical proofs, independently reviewed
derivations, and exact computational checks. The full upstream Lean build
was not rerun. The new results have not been formalized in Lean;
formalization/PLAN.md is an explicit future proof decomposition.
No extension-field enumeration or worldwide novelty certification is claimed.

## File integrity

SHA256SUMS.txt covers the deliverable files other than itself.
Temporary LaTeX build files and rendered review images are excluded.
