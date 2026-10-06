ROBUST CHOICES THAT NEVER SETTLE
An exact finite-infinite puzzle about resilience, choice, and randomness
Prepared for Vladimir Reshetnikov, 5 October 2026

READING
  robust_choices.pdf       Complete research article.
  robust_choices.tex       Complete LaTeX source; bibliography is included.
  figures/                 Figure used by the article, in PDF and PNG formats.

REPRODUCIBILITY
  code/verify.py           Exact finite verifier (Python standard library).
  code/generate_figures.py Recreates the plot from exact binomial fractions.
  data/exact_verification.json  Actual verification report.
  data/majority_table.csv       Exact rational values and readable decimals.
  data/verification_run.txt     Successful run transcript.

To rerun finite verification from this directory:
  python3 code/verify.py

To regenerate the figure (requires matplotlib and numpy):
  python3 code/generate_figures.py

To compile the article (ordinary TeX Live packages suffice):
  pdflatex -interaction=nonstopmode -halt-on-error robust_choices.tex
  pdflatex -interaction=nonstopmode -halt-on-error robust_choices.tex
Run an additional pass if LaTeX requests updated cross-references.

MATHEMATICAL STATUS
The finite optimum is a consequence of Kleitman's diameter theorem.
The article proves the antipodal reduction, sharp prefix inequality and its
matching constructions, mixing/oscillation results, the open bounded-density
recoding theorem, probability/category contrasts, a Hamming-code separation
of one-edit and two-edit resilience, and the biased-product extension.
Kakutani's theorem is an explicit input for the bias classification.
General mixing and subsequence phenomena are classical; the article makes no
unverified claim of worldwide novelty or a breakthrough on a published open
problem. Further research questions are labeled proposals.

The exact finite program is a useful independent check, not a formal proof of
the infinite-dimensional theorems. No new Lean or Rocq verification is claimed.

PROVEIT SNAPSHOT
  https://github.com/VladimirReshetnikov/ProveIt
  revision 3b9458b31f459b480ab43a068d7cc56f4cfdbb28
  SetTheory/Cardinals/Cardinals/Countable/GenericErgodicity.lean

All citations and detailed scope/assumption statements appear in the article.
