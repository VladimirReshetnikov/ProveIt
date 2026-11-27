ELECTRICAL LAWS FOR GRAPH-COUPLED ZEROS
26 November 2026

Start with report.pdf.  Complete LaTeX source is report.tex plus sections/.

Main result
-----------
A rooted-forest combination of real-rooted polynomials and their first
derivatives has an explicit symmetric matrix model.  In ordered matching,
its zeros lie to the left of the critical points of the input product.
The exact mean displacement is

    sum_{i<j} d_i*d_j*R_ij / (N*(N-1)),   N = sum_i d_i,

where R_ij is the effective resistance of the weighted graph.  This value
does not depend on the original zero locations.  A positive edge increment
has an exact positive rank-one matrix update and a second displacement law.

The paper also proves a direct entire-function extension, an exact shared
zero/collision multiplicity formula, and an interval zero-count identity.
The supplied Dirichlet GRH theorem supplies completed Dirichlet L-functions
to this construction, including primitive complex characters.  An explicit
three-character example uses conductors 3, 4, and 5.

Proof and novelty status
------------------------
The paper includes full human-readable proofs.  Exact rational finite
identities have been checked by the included SymPy script.  The new results
are not Lean formalizations.  The complete upstream GRH build was not rerun.

The forest determinant, differentiator compression, stability theory, and
matrix interlacing ingredients are classical and credited.  The precise
electrical transport formulation is the candidate new contribution.  It
was not found in the screened ProveIt material or the targeted literature
search.  Worldwide publication priority has not been established.

The resistance/centroid sums apply to finite polynomial models.  No
unregularized infinite displacement sum for Dirichlet zeros is claimed.

Contents
--------
report.pdf, report.tex, sections/  Paper and all its source sections.
code/verify_graph.py              Exact rational verification.
code/illustrate.py                Reproducible numerical figures.
code/build_pdf.sh                 Standard TeX Live build command.
checks/graph_checks.json          Exact recorded finite checks.
checks/graph_checks.txt           Recorded checker output.
checks/illustrations.json         Numerical figure metadata.
checks/transport_plot_data.csv    All plotted transport data.
figures/                         Vector PDFs and PNG previews.
provenance/                      Source audit, comparison, source identities,
                                 literature search and proof review.
requirements.txt                 Python versions used.
SHA256SUMS                       Digests of every other delivered file.

Reproduction
------------
From this directory:

    python3 code/verify_graph.py
    python3 code/illustrate.py
    sh code/build_pdf.sh

A normal TeX Live installation with latexmk and the listed LaTeX packages
builds the PDF.  Python dependencies are recorded in requirements.txt.
The checker writes checks/graph_checks.json; terminal output can be captured
separately.  The proof does not rely on numerical zero tables.

Sources
-------
grh-lean commit: 72fead102f663d5c7a407964a13dc0cf9d977207
ProveIt commit:  4d7990202f9f106b2ffe8c209f073ad01d5e1987

The comparison screened all 61 organized packet READMEs and the relevant
text in 39 later ZIPs within Analysis/GeneralizedRiemannHypothesis.  This
was not a complete independent proof audit of all 100 packets.  Original
source archives are not redistributed; the provenance manifests retain
their exact repository identities.
