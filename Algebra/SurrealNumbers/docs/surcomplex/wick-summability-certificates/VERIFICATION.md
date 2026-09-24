# Verification record

## Mathematical evidence

The paper includes proofs of all proposed results. Its imported foundational
inputs are identified: the classical positive-support lemma for Hahn series and
standard surreal normal-form laws. Classical finite combinatorics and strict
elimination are also reproved for the exact conventions used.

The main equivalence is proved in both directions. The sufficiency proof handles
arbitrary Hahn-unit tails, not just monomial inputs. Necessity uses exact nonzero
leading coefficients and a repeated integer incidence vector. The connected
obstruction proof uses a graph construction, not an inference from sampled
connected coefficients.

The paper explicitly records the cancellation counterexample and the failure of
the connected-domain statement when linear vertices are allowed.

There is no proof-assistant verification or peer review.

## Executed finite checks

`python3 code/verify.py` completed successfully with seed 20260922.
The actual category counts and sample certificates are in `data/verification.json`.
There are **7,684 counted finite test cases**. This is not a count of proved
infinite statements. Additional exact certificate assertions are not included in
the case count.

The tests include comparisons against independently formulated closed criteria,
a moment recurrence independent of the factorial formula, direct connected
pairing enumeration, and exact isotropic cancellation.

The executed certificate tests use lexicographic rational value groups of ranks
one, two, and three. They do not computationally establish arbitrary-rank claims.

## Typesetting and artifact checks

The LaTeX was compiled with `latexmk -pdf -halt-on-error -interaction=nonstopmode`.
The final PDF has 27 pages. The final log was checked for undefined references,
multiply defined labels, overfull boxes, and warnings. Page renders were inspected,
including the title, contents, theorem pages, connected-diagram construction,
examples, tables, and bibliography.

No fonts or third-party research PDFs are included as standalone files.

## Reproduction

From the package root:

```sh
python3 code/verify.py
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

The Python tests require Python 3.10 or later and use only its standard library.
Do not use Python's `-O` flag; it would disable internal assertions.

For independent certificate checking, use Appendix A: substitute the proposed
balancing vector into the inequalities, or verify the integer witness's
nonnegativity, incidence equation, and nonpositive weight directly.
