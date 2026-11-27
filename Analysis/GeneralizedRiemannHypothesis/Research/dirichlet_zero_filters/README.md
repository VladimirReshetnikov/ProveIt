# The shortest positive average that cancels two Dirichlet zeros

The 12-page paper proves the shortest two-frequency cancellation formula, its distribution along every fixed primitive Dirichlet zero sequence, the endpoint laws, and a secondary arithmetic term. A separate theorem gives the sharp order of the wide-step zero-free interval deficit and transfers it to a growing collection of actual Dirichlet zeros.

## Files

| File | Contents |
| --- | --- |
| paper.pdf | Complete compiled research paper |
| paper.tex | Complete LaTeX source in a single file |
| pair_width.pdf | Vector figure used by the source |
| pair_examples.py and pair_results.txt | Two-frequency optimizer, checked moments, zeta examples, and optional figure generation |
| law_profile.py and law_results.txt | Distribution function, median, and endpoint constants |
| progression_check.py and progression_results.txt | Nine rational certificates for finite progression bounds |

## Reproducing the results

With a standard LaTeX installation, run the following commands in this directory.

~~~sh
pdflatex -halt-on-error paper.tex
pdflatex -halt-on-error paper.tex
~~~

These commands reproduce the numerical and certificate outputs with Python 3.

~~~sh
python3 pair_examples.py
python3 law_profile.py
python3 progression_check.py
~~~

The first two programs evaluate the proved formulas in floating point. The progression checker uses rational arithmetic with outward rounding and verifies positivity on whole intervals. Matplotlib is optional and can regenerate the included figure.

~~~sh
python3 pair_examples.py --plot
~~~

## Source snapshot and verification

The paper inspects ProveIt commit b6253012cf30c80a989c871906e097a27f23a27c and the vendored lsernau/grh-lean readable edition at upstream commit 72fead102f663d5c7a407964a13dc0cf9d977207. The mathematical input is its critical-line theorem for Dirichlet characters. The new results have human-readable proofs. The Lean package was not independently rebuilt for this paper. Immutable source links and the primary mathematical references appear in the bibliography.
