FACTORIAL CAUCHY MODES FOR THE SUBEXPONENTIAL 3-SAT ALGORITHM
Research note prepared for Vladimir Reshetnikov — October 26, 2026

MAIN RESULT

Replace the geometric-series modes in the cited manuscript's Boolean tensor
contraction by a finite integral Cauchy separation. The certified weight at
mode index b becomes

    w_b = 1 + b + 2*v_2(b!) = 3*b + 1 - 2*popcount(b).

This gives a 1/sqrt(3) ratio of leading logarithmic abstract mode-enumeration
counts, compared with geometric weights b+1. The report proves a correspondingly
smaller explicit global contraction upper-bound coefficient, using matched
parameters and a slightly deeper leaf cutoff for both compared bases.

SCOPE AND LIMITATIONS

* The general 3-SAT order remains polynomial(n,m) times
  2^O(n log log n / sqrt(log n)). A better power of log n is NOT proved.
* The comparisons concern certified enumeration work and explicit upper bounds,
  not a universal ratio of actual SAT runtimes.
* The new lemmas are natural-language proofs with exact computational checks.
  They have NOT been formalized or checked in Lean.
* code/cauchy_modes.py is a reusable kernel prototype, NOT a complete SAT solver.
* The original paper's unchanged contraction/reduction arguments are assumed.
* The identity is classical in character. External priority or novelty of this
  specific application has not been established.

CONTENTS

report.pdf                       Complete mathematical report.
report.tex                       LaTeX source for that report.
code/cauchy_modes.py              Exact rational and modular mode features.
code/verify_modes.py              Local algebra and tiny contraction checks.
code/count_modes.py               Exact colored weighted-partition counts.
code/build_exhibits.py            Recreates tables and the optional figure.
results/verification.json         Executed arithmetic checks and scope.
results/mode_counts.json, .csv    Exact abstract tuple counts (not SAT timings).
results/*.tex                    Tables included by report.tex.
figures/mode_entropy.pdf, .png    Figure generated from the exact count data.
source_manifest.json             Source snapshot and verified Git blob hashes.
Makefile                         Reproduction and PDF targets.

REPRODUCTION (from this directory)

Python 3.10 or newer is sufficient for the core code; it has no third-party
dependencies. The included tests were run under the version recorded in
results/verification.json.

    python3 code/verify_modes.py
    python3 code/count_modes.py
    python3 code/cauchy_modes.py

The default exact-count computation uses precisions through 4096 and family
counts 1 and 4. The strict convention is total weight < precision. The main
mode-count files do not impose a finite tile cutoff; finite-cap diagnostics
are separately recorded in verification.json.

To recreate the figure and report tables, install matplotlib if needed, then:

    python3 code/build_exhibits.py

To rebuild the PDF, use a standard TeX Live installation with latexmk,
pdflatex, Latin Modern, AMS mathematics, microtype, booktabs, enumitem,
fancyhdr, listings, and hyperref:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The prebuilt figure and generated table sources are included, so rebuilding
the PDF does not require Python or matplotlib.

Equivalent Makefile targets: make verify, make counts, make exhibits, make pdf.

SOURCE

OpenAI, The Exponential Time Hypothesis is False, revised October 25, 2026.
https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026

The original manuscript files are not redistributed in this archive. The
source manifest records their paths, hashes, and retrieval snapshot.
