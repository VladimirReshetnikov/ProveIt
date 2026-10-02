# Lexicographic Orders of Well-Orderings of the Continuum

Research manuscript prepared for Vladimir Reshetnikov, 2 October 2026.

## Contents

- `article.pdf`: the typeset comprehensive article.
- `article.tex`: the complete self-contained LaTeX source, including references.
- `finite_checks.py`: exact finite tests, using only Python's standard library.
- `finite_checks.json`: the actual test output (552,450 checks passed).
- `RESEARCH_STATUS.md`: scope, source provenance, and verification limits.

## Mathematical setting

Work in ZFC. Let kappa be the initial ordinal of the continuum cardinal.
W is the order of all exhaustive injective enumerations of R by ordinals of
cardinality kappa, compared at their first unequal real entry. It represents
all well-order relations on R, not just their ordinal types. W_alpha is its
fixed-length stratum.

The actual index A in the checked Kanovei–Shelah construction consists instead
of maps kappa -> P(N) whose range is an ultrafilter, with lexicographic comparison.
The manuscript studies both objects without identifying them.

## Selected conclusions

Every ordinal beta embeds into W exactly when beta < kappa^+; the same holds for
reverse ordinals, W_kappa, and A. Every linear order of size at most kappa embeds.

Every stratum has an exact equimorphism classification:
W_(lambda+n) is equimorphic with the lexicographic product of the binary cube
2^lambda and an n!-element chain, where lambda is a limit ordinal and n is finite.
The article also gives the exact embeddability comparison between strata.

W contains the binary lexicographic cube of length theta exactly for theta < kappa^+,
but its own least binary coding length is kappa^+. In contrast, W_kappa and A
are equimorphic with the binary cube of length kappa.

The lexicographic power W^gamma embeds back into W exactly for gamma < kappa^+.
The full order has finite permutation blocks, jumps, and 2^kappa isolated points.
The fixed initial-cardinal stratum and A are dense, with distinct global cofinalities.

The article provides proofs, completion results, and ten further research topics.

## Build the PDF

Use a TeX distribution with amsmath, amsthm, mathtools, newtx, geometry,
microtype, xcolor, booktabs, array, tabularx, enumitem, fancyhdr, tcolorbox,
hyperref, and cleveref. These are available in standard full TeX Live installations.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex article.tex` at least twice (and again when requested
for cross-references). No BibTeX step or external image files are needed.

## Reproduce the finite checks

Python 3.10 or newer, with no third-party dependencies:

```sh
python finite_checks.py --output finite_checks.json
```

The tests cover pair swaps, finite cut codes, permutation adjacency, cylinder
sizes and convexity, full-child cuts, concatenation, and finite binary capacities.
They are not machine verification of the infinitary proofs. No Lean or Rocq
formalization is included. The written mathematical proofs remain subject to review.
