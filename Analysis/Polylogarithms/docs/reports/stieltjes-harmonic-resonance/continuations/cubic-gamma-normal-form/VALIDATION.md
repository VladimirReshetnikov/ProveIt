# Validation record

## Mathematical scope

The all-weight cubic result is proved by the variational recurrence and
explicit indeterminate-index polynomial identities in Sections 2–5.
Finite regression tests are separate from that proof. The all-derivative-
order extension in Conjecture 9.1 remains unproved.

## Exact replay

`verification/verify_exact.py`: PASS, including the full 31 normal-form
decompositions through weight 30, 973 cubic coefficient comparisons, and
four symbolic density identities with the index treated as an indeterminate.

`verification/verify_endpoints.py`: PASS, including four exact spectral
integral reductions, four rational coefficient families, twelve partial-
fraction identities, and agreement of the printed H8 and N11 with the
independent rational certificates.

The 438 exploratory higher-index comparisons are recorded in their own
JSON field. Their success does not change the conjecture's status.

## Numerical replay

`verification/verify_numeric.py`: PASS, 30 checks. Most use 50 working
decimal digits and a scaled residual threshold of 1e-38; the generalized
Stieltjes quadrature uses 35 digits and a threshold of 1e-28. The latter
recorded residual is approximately 1.32e-36. No interval certification is
claimed. Exact values and all configured tolerances appear in the JSON.

## Document build and review

The modular article and the single-file standalone source both compiled
successfully with latexmk/pdfLaTeX. The standalone source was compiled in
an isolated directory with no modular files present. The resulting PDFs
have exactly matching extracted text. The final article has 23 pages.

The final LaTeX log contains no undefined references, overfull boxes, or
warnings. Every final page was rendered through pdftoppm and visually
reviewed in contact sheets; the main theorem and the explicit integral
page also received larger renders. The main theorem was moved so that its
statement is not split across a page boundary. Final-only artifacts are
included; temporary TeX files and raster review images are not required by
the article and are excluded from the ZIP.

## Limits

No Lean, Isabelle, or other proof assistant was used. No claim of global
priority, exhaustive incoming archive audit, arithmetic period independence,
or certified numerical error bounds is made. No remote repository file was
changed.
