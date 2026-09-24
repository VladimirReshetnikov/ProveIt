# A marked-cycle proof of the trapezohedral domination conjecture

**Research manuscript — OEIS A381190**

Read `article.pdf`; its complete, self-contained LaTeX source is `article.tex`.
The manuscript proves the generating function still labeled conjectural in
the inspected OEIS record and derives additional enumeration and limit laws.
The mathematical proof is complete as presented. Literature priority has not
been independently established; the work is not peer-reviewed or formalized
in a proof assistant.

This directory is the **union of two independently prepared packages** on the
same conjecture. See "Provenance" below.

## Main result

For the n-trapezohedral graph (n >= 3), let a_n count dominating vertex subsets
that are inclusion-minimal among **all dominating sets** and induce a connected
subgraph. This is not the different notion "minimal connected dominating set."

Let p_0=1, p_1=0, p_2=1 and p_m=p_(m-2)+p_(m-3). Then

    a_n = 2*n*(2*p_(n-2) + p_(n-3)).

Equivalently, using the OEIS indexing of A000931,

    a_n = 2*n*(2*A000931(n+1) + A000931(n)).

The proof classifies the sets by a cyclic arrangement of gaps of lengths 2
and 3, with a restricted marked edge. It handles n=3 explicitly. Consequences
include an exact size/type distribution, a closed finite binomial sum, strict
log-concavity, an unbiased sampler, a Binet formula, two exact nearest-integer
evaluations (one for a_n/(2n) from n>=4, one for a_n itself from n>=45), and a
central limit theorem for size.

## Contents

- `article.tex`, `article.pdf`: the manuscript, including full proofs,
  three TikZ diagrams, source attribution, provenance, and reproduction
  instructions.
- `code/research.py`: standard-library exact counts, size distributions,
  structural generation, graph-based tests, and uniform sampling.
- `code/exhaustive.cpp`: independent, portable C++17 all-subsets enumeration.
- `code/verify.py`: a **second, separately written** standard-library
  all-subsets enumeration, from the incoming package. It shares no code with
  the other two. Keeping both Python implementations is deliberate: their
  independence is what the agreement is worth.
- `code/verify_symbolic.py`: optional SymPy/mpmath symbolic and numerical audit.
- `data/counts.csv`: totals, normalized totals, and topology counts, n=3..1000.
- `data/terms.csv`: the same totals, produced independently by `code/verify.py`.
- `data/b381190.txt`: the total sequence in OEIS b-file style.
- `data/size_distribution.csv`: counts by size and topology, n=3..100, indexed
  by the number k of zeros (written by `code/research.py`).
- `data/size_distribution_by_cardinality.csv`: counts by size, n=3..100,
  indexed by the cardinality d (written by `code/verify.py`). Renamed on merge
  to avoid a filename collision; the two files are independent computations of
  the same numbers and agree on all 882 rows.
- `data/exhaustive.csv`: every accepted vertex mask for n=3..11 (C++ run).
- `data/exhaustive_checks.json`: per-n exhaustion record for n=3..10
  (`code/verify.py` run).
- `data/certificates_n5.json`: all 30 sets for n=5 with a private neighbor for
  every selected vertex. Uses the incoming package's one-based labels
  `u, v, a_1..a_n, b_1..b_n`; the article uses `N, S, a_0..a_(n-1),
  b_0..b_(n-1)`, with `u = N`, `v = S`, `a_i = a_(i-1)`, `b_i = b_(i-1)`.
- `data/asymptotics.json`: computed constants and sample errors.
- `data/oeis_a381190_3_42.txt`: the 40 attributed source terms, kept separate
  from all generated data.
- `notes/sources.md`: retrieval and attribution notes.
- `notes/oeis_submission.txt`: concise, UNSUBMITTED draft for OEIS discussion.
- `oeis_update.txt`: a suggested formula and compact proof note, not submitted.
- `provenance/`: the incoming package's problem-selection audit. See below.
- `verification/`: recorded exact tests, symbolic tests, the two exhaustion
  transcripts, environment, source audit, and PDF-build/inspection summary.
- `requirements-optional.txt`: dependencies only for the optional audit.
- `Makefile`: convenience targets on systems with make, g++, Python, and TeX.

All generated counts are computed from the proof, not downloaded from an OEIS
b-file. The 40 published initial values are separately embedded as comparison
fixtures with source attribution in the manuscript and source audit.

## Run the verifications

From this directory. First, the standard-library stack of the base package:

    python code/research.py verify
    python code/research.py data --maximum 1000
    python code/research.py sample 20 --seed 381190

The first command performs a Python-only exhaustive check for n=3..7 and
checks the exact formulas through n=1000. It requires no third-party package.

Second, the independent standard-library verifier from the incoming package,
which exhausts n=3..10 with a different program:

    python code/verify.py --brute-max 10 --max-n 1000

Do not run it under `python -O`: its checks are implemented as assertions.
`--brute-max` accepts 3..11 and `--max-n` accepts 50..10000; the upper settings
take much longer. A faster diagnostic run is
`python code/verify.py --brute-max 7 --max-n 100`. The program overwrites the
generated data files it owns, but never the source terms, the article, the
recorded draw, or the base package's own data files.

Third, the larger, independent C++ exhaustion:

    g++ -O3 -std=c++17 -Wall -Wextra -pedantic code/exhaustive.cpp -o exhaustive
    ./exhaustive 11 > data/exhaustive.csv
    python code/research.py verify --exhaustive-csv data/exhaustive.csv --report verification/exact_checks.json

On Windows with PowerShell 7 and g++, use `./exhaustive.exe` for the executable.
The C++ source also avoids compiler-specific bit-counting intrinsics, but only
the recorded GCC build was tested here. Each accepted row records n, set size,
induced edge count, and the complete integer vertex mask.

`code/research.py` and `code/exhaustive.cpp` use the vertex numbering
N=0, S=1, a_i=2+2*i, b_i=3+2*i. A sample is printed as a set of these integer
vertex indices. `code/verify.py` uses its own numbering and its own one-based
labels, as described above. Each of the three acceptance predicates uses only
the graph, closed neighborhoods, private neighbors, and a connectivity
traversal; none uses the classification to prune subsets.

`make test`, `make test-independent`, `make test-symbolic`, and `make test-all`
are optional conveniences for the three stacks.

## Optional symbolic audit

    python -m pip install -r requirements-optional.txt
    python code/verify_symbolic.py

The exact algebraic checks include the claimed generating functions, the
Perrin weighting identity, the Binet weights via a cubic-field matrix trace,
and rational inequalities proving the rounding bound. Floating-point checks
use 180 decimal digits through n=1000 and are supplementary, not substitutes
for the proofs.

## Build the PDF

Use a TeX Live or MiKTeX installation with newpx, amsmath, amsthm, mathtools,
TikZ, tcolorbox, listings, microtype, hyperref, cleveref, and the other packages
listed in the preamble. No external images, bibliography database, shell escape,
or font files supplied by this archive are needed. No BibTeX or Biber run is
needed.

    latexmk -pdf -interaction=nonstopmode article.tex
    latexmk -c

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` three times; three passes reliably settle the contents and
cross-references. `make pdf` and `make pdf-pdflatex` do these two things.

## Recorded checks

The independent C++ program examined all 22,369,536 subsets for n=3..11 and
accepted 926 sets in total. The independent Python verifier examined all
subsets for n=3..10 and reproduced every one of those counts set-by-set on the
eight values of n the two runs share. The full sets of vertex masks matched
structural generation exactly, as did their size/topology counts. All 40
published terms matched. The two term tables agree digit for digit on all 998
shared values of n, including the 126-digit a_1000, and the two size
distributions agree on all 882 shared rows. Exact identities, endpoint counts,
divisibility, and strict log-concavity were tested through n=1000; 900 sampled
sets passed the independent membership test. See the JSON reports and the two
transcripts in `verification/` for the actual saved results.

The PDF was compiled without reported overfull boxes or unresolved references,
rendered, and visually inspected. No automated submission to OEIS, publication,
or external account action was performed.

## Provenance

This directory merges two independently prepared packages that proved the same
theorem by the same argument:

- **`trapezohedral-minimal-dominating-sets`** (this directory; the package that
  was already in the collection). It supplies the manuscript, the
  classification and marked-gap bijection that are kept as the single proof,
  the induced-topology refinement, the trivariate generating function, the
  Perrin identity, strict log-concavity, the extremal multiplicities, the
  gamma_c separation, the central limit theorem and cumulant algorithm, the
  uniform sampler, the C++ exhaustion, and the symbolic audit.
- **`trapezohedral-connected-minimal-domination`** (the incoming package, now
  removed). Everything it proved that was not already here has been carried
  over and is listed in the article's "Provenance of this archive" appendix:
  the finite binomial sum, the nearest-integer formula for a_n itself with its
  integer certificate 360*7^45 < 8^45, the expanded size-refined rational form,
  the explicit evaluations Q(0)=1, Q(-2/3)=23/27, Q(-2)=5 behind the
  minimality of order 6, the worked n=5 certificate, the asymptotic error
  table, `code/verify.py`, and the data it produces.

Because the two proofs are the same argument, they are **not** presented as
alternative proofs. The incoming package's "marked-block" reading of the
bijection is recorded in one place in the article as the equivalent blockwise
reading of the same map.

Three notational conversions were applied to everything imported, and each one
would have silently corrupted a formula if skipped: the incoming `(r, s)` for
the numbers of length-2 and length-3 blocks is this package's `(s, t)`, so the
incoming `s` is this package's `t`; the incoming constant `C` is this package's
`K = 2*C(alpha)`, twice its `C(alpha)`, and the incoming `lambda` is `alpha`;
and the incoming size index `d` relates to this package's `k` by `k = n-d+2`.

### The incoming package's problem-selection audit

`provenance/` holds the incoming package's record of how its author chose this
problem: an ordered four-entry shortlist (A225114, A244475, A289587, A381190)
fixed before the draw, one `secrets.randbelow(4)` call returning 3 (zero-based,
selecting candidate 4), and zero rerolls. `provenance/select_candidate.py`
refuses to overwrite the recorded draw. This is provenance for that package's
selection, not a fact about A381190, so it is kept out of the merged article
body and out of `data/`. It should not be attached to this package's own
problem choice, which was made differently.

The randomness came from the operating system and was not generated from a
published deterministic seed. The record therefore documents the actual
selection, not a seed-replayable experiment. The three unselected conjectures are not claimed to be
solved here.

## Status and limitations

The generating function is proved by the mathematical argument, not by finite
agreement alone. Exhaustive checking ends at n=11 in the C++ run and at n=10 in
the archived standard-library run. The decimal asymptotic calculations are
diagnostics, not interval certificates; both nearest-integer claims have
separate uniform proofs. The threshold 45 in the unnormalized nearest-integer
formula is sufficient; no minimality claim is made for it. The operation counts
quoted for the recurrences are arithmetic-operation counts, not unit-cost
bit-complexity claims for unbounded integers; the sampler's uniformity is
established by proof, not by a frequency experiment.

This is not a Lean/formal proof-assistant artifact and has not been
independently peer-reviewed. Targeted searches did not locate an earlier proof;
that is not a guarantee of literature priority. The OEIS entry was still
conjectural when retrieved, but first-in-the-literature priority is not
claimed. No OEIS edit or submission has been made. The three unselected
conjectures are not claimed to be solved here. Source terms and attribution are
retained separately from the newly generated computational data. The known
Padovan composition interpretation and Perrin maximal-independent-cycle
interpretation are explicitly credited rather than claimed as new.
