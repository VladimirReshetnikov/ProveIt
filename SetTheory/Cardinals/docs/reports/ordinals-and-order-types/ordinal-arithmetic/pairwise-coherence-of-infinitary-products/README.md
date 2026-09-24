# Pairwise Coherence Does Not Guarantee Completion of Ordinal Products

**A two-element counterexample and an unbounded hierarchy of nesting obstructions**  
Research report prepared for Vladimir Reshetnikov, September 20, 2026.

## Main result

The report addresses the pairwise-coherence sufficiency question in Paolo
Lipparini, *Noncommutative infinitary semigroups*, arXiv:2605.28413v1,
Remark 7.1(b).

On C2 = {e, a}, retain every finite group product and define every infinite
all-e product to be e. Leave every other infinite product undefined. This
partial system satisfies the full pairwise regrouping condition, even for
arbitrary partitions, but has no injective extension defining all finite and
omega-indexed products. Two elements is minimal.

The nonembedding mechanism is the known inverse obstruction in Lipparini's
Proposition 5.1. The report's contribution is the coherent partial-domain
construction and proof that it answers the stated sufficiency question,
together with the generalizations below. Publication priority has not been
independently established; the report is unrefereed.

## Additional results

For any monoid M, the same canonical partial domain P(M) satisfies ordered
pairwise coherence. When M is directly finite (in particular, when M is finite
or commutative), P(M) admits a complete extension exactly when its unit group
is trivial. In the positive case, one additional absorbing element suffices;
the report gives an explicit product for all linearly indexed words and proves
regrouping for arbitrary convex partitions.

For every finite r >= 1, a separate partial system with 3r + 4 elements satisfies
coherence through depth r but fails at depth r + 1. All nonempty constant
products of all elements are defined. This family has a partial finite product;
it does not establish the same unbounded-depth assertion under a total-finite-
product hypothesis. The two-element example does have all finite products.

## Files

- `ordinal_product_coherence.pdf`: the 19-page article, including full proofs,
  two certificate tables, source attribution, and a logical audit.
- `ordinal_product_coherence.tex`: complete LaTeX source, including bibliography.
- `verify.py`: exact verification code using only the Python standard library.
- `verification_results.json`: output from an actual successful run.
- `SOURCE_NOTES.md`: consulted versions, exact target, and attribution boundaries.
- `Makefile`: document and verification targets.

No third-party papers or font files are included.

## Reproduce the checks

Python 3.9 or later is sufficient. In the extracted directory:

```text
python3 verify.py --output verification_results.json
```

On Windows, `python verify.py --output verification_results.json` works with a
suitable Python interpreter on PATH. No network access or external libraries
are used.

The program checks every C2 word of length at most 10 and all its convex
partitions: 2,047 words and 699,051 regrouping checks, including the empty case.
It also checks the two incompatible omega-word evaluation trees using an exact
finite-prefix/period representation, not a finite truncation.

All labeled monoids of sizes 1 through 4 with identity fixed at label zero are
enumerated. The associative-table counts are 1, 2, 11, and 156; the counts with
trivial unit group are 1, 1, 8, and 113. The fork invariants are checked for
parameters k = 3 through 16, and the complete 26-content depth-two certificate
for the ten-element fork is generated.

These checks supplement the proofs. The universal statements about arbitrary
linear orders, every monoid, and all fork parameters are proved in the article,
not inferred from bounded testing. No proof-assistant formalization is included.

## Rebuild the PDF

A standard TeX Live installation with the packages listed in the source is
sufficient. The bibliography is embedded; BibTeX is not required.

```text
pdflatex -interaction=nonstopmode -halt-on-error ordinal_product_coherence.tex
pdflatex -interaction=nonstopmode -halt-on-error ordinal_product_coherence.tex
```

Alternatively, run `make` for the PDF and `make verify` for the checks.
The delivered PDF was compiled successfully, rendered, and visually checked.
