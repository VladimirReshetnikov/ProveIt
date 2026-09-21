# A proof of the generating-function conjecture for OEIS A381190

Date: September 20, 2026.

## Result

For n >= 3, let a_n count the vertex subsets of the n-trapezohedral graph
that are inclusion-minimal dominating sets and induce connected subgraphs.
The conjecture attributed in OEIS to Joerg Arndt (January 7, 2026) is proved:

    sum(a_n*x^n, n>=3)
      = -2*x^3*(4*x^5+8*x^4+4*x^3-9*x^2-8*x-3)/(x^3+x^2-1)^2.

The key coefficient formula is

    a_n = 2*n*[x^n] (2*x^2+x^3)/(1-x^2-x^3).

The article gives the complete combinatorial proof and its converse,
a finite sum, cardinality refinements, recurrences, a three-root formula,
an asymptotic, and a nearest-integer formula valid for every n >= 45.

Important conventions: minimality is among ALL dominating subsets, not
only connected ones. Sets are actual vertex subsets, not symmetry classes.
The graph has 2*n+2 vertices, and n=3 is the cube.

## Read or rebuild the article

- `article.pdf`: compiled article.
- `article.tex`: self-contained LaTeX source, including the bibliography.

A TeX Live or MiKTeX installation with the standard packages named in the
preamble is sufficient. With latexmk installed:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively, run `pdflatex article.tex` three times. No BibTeX or Biber
run is needed. The included Makefile offers `make pdf` and `make clean`.
The clean target preserves the PDF and all research data.

## Reproduce the checks

Python 3.10 or later, standard library only; no network access or package
installation is required. From this directory, run:

    python3 code/verify.py --brute-max 10 --max-n 1000

On Windows, use `python` or `py -3` in place of `python3`, as appropriate.
Do not use `python -O`: assertions implement the verification checks.
The included transcript was generated with Python 3.13.5.

The program:

1. Exhaustively handles all 2^(2*n+2) subsets for 3 <= n <= 10, rejecting
   the empty subset immediately and testing domination, all one-vertex
   deletions, and induced connectedness for the other subsets.
2. Independently generates the cyclic-word classification and checks
   exact equality of the families of subsets, plus size distributions.
3. Compares formal division of the conjectured rational function, the
   binomial sum, the Padovan-type recurrence, both derived recurrences,
   and the sum of size-refined counts through n=1000.
4. Checks all 40 transcribed OEIS terms, for n=3..42.
5. Checks exact rational inequalities used in the rounding proof and,
   separately, high-precision numerical rounding for n=45..1000.

The exhaustive search is exponential; the largest default case examines
4,194,304 subsets and uses about 16 MiB for its coverage array, plus
interpreter and other data. `--brute-max` accepts 3..11 and `--max-n`
accepts 50..10000. The upper settings can take much longer. Running the
verifier overwrites the generated data files, but never the candidate
list, recorded selection, source terms, article, or source notes.

A smaller diagnostic run is:

    python3 code/verify.py --brute-max 7 --max-n 100

The Makefile's `make verify` runs the default full checks. To replace the
saved transcript deliberately, redirect or pipe the output to
`data/verification.txt`.

## Random-selection audit

The candidate order was fixed first:

1. A225114: skew partitions, continued-fraction generating function.
2. A244475: fifth-largest distinct Stern-triangle values, rational GF.
3. A289587: restricted 321-avoiding permutations, algebraic GF.
4. A381190: connected minimal domination in trapezohedral graphs, rational GF.

One call to `secrets.randbelow(4)` returned 3 (zero-based), selecting
candidate 4. There were no outcome-dependent rerolls. The original list
and draw are `data/candidates.json` and `data/selection.json`.

The draw used operating-system randomness, not a published deterministic
seed. The record is an audit of the actual result, not a seed-replayable
random experiment. `code/select_candidate.py` refuses to overwrite the
existing selection. Do not delete the recorded draw to reproduce the
mathematics: `verify.py` reads it and does not draw again.

## Files

- `code/verify.py`: independent graph enumerator and checks.
- `code/select_candidate.py`: original one-draw utility with overwrite guard.
- `data/verification.txt`: captured successful run.
- `data/exhaustive_checks.json`: exact counts and size distributions.
- `data/terms.csv`: a_n for n=3..1000.
- `data/size_distribution.csv`: a_(n,d) for n=3..100.
- `data/certificates_n5.json`: all 30 sets for n=5 and private neighbors.
- `data/asymptotics.json`: computed constants and sample errors.
- `data/oeis_a381190_3_42.txt`: attributed source terms.
- `notes/sources.md`: retrieval and attribution notes.
- `notes/candidate_formulas.md`: conjectural formulas in the shortlist.
- `notes/oeis_submission.txt`: concise, UNSUBMITTED draft for OEIS discussion.

## Status and limitations

The generating function is proved by the mathematical argument, not by
finite agreement alone. Exhaustive checking ends at n=10 in the archived
run. The decimal asymptotic calculations are diagnostics, not interval
certificates; the nearest-integer claim has a separate uniform proof.
This is not a Lean/formal proof-assistant artifact and has not been
independently peer-reviewed. The OEIS entry was still conjectural when
retrieved, but first-in-the-literature priority is not claimed. No OEIS
edit or submission has been made. The three unselected conjectures are
not claimed to be solved here. Source terms and attribution are retained
separately from the newly generated computational data.
