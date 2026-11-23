# The Mertens function in intuitionistic primitive recursive arithmetic

Read **mertens-ipra.pdf**. Its first page maps the results to the sections. The paper includes the numerical definitions, proofs, primitive recursive bounds, and the distinction between the semantic Lean theorems and an object-language iPRA derivation.

## Files and reproduction

| Files | Contents |
| --- | --- |
| report.tex and the other .tex files | Complete LaTeX source of the paper. The main file inputs the sections in order. |
| figures/mertens-quotient.pdf | Vector figure used by the main source. |
| lean/ | Standalone, standard-library Lean sources. See its README for exact build commands. The same files passed Lean 4.19.0 and 4.32.0. |
| code/check_mertens.py | Linear sieve, independent divisor inversion, two isolated-value methods, the historical range and exact table comparisons. |
| code/check_identities.py | Independent exact checks for Redheffer, Farey, Chebyshev, totient, floor and ordered-product formulas. |
| code/plot_mertens.py | Optional cover figure regeneration using Matplotlib. |
| verification/ | Exact finite results, the two kernel audits, and the replay record for the upstream rational zero certificate. |

Run these commands in the extracted directory.

~~~sh
pdflatex -jobname=mertens-ipra -halt-on-error report.tex
pdflatex -jobname=mertens-ipra -halt-on-error report.tex
python3 code/check_mertens.py
python3 code/check_identities.py
~~~

The mathematical checks require Python 3.9 or later and its standard library. Only regeneration of the bundled figure requires Matplotlib. The pinned ProveIt revision, exact imported mathematical results, verification scope and primary references are in the paper. The iPRA arguments concerning analytic quantities use finite rational observations, explicit clocks and separation witnesses as specified in the statements. The compact form of the RH criterion proves an equivalence between two arithmetic conditions.
