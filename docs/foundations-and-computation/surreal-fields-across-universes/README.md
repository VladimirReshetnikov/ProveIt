# Forcing, Omitted Cuts, and Old Surreal Fields

**Ordinal-sequence spectra, surcomplex conjugation, and a Boolean completion of reverse simplicity**

Research article prepared with ChatGPT, 22 September 2026.

## Files

- `article.pdf`: the 25-page typeset article.
- `article.tex`: self-contained LaTeX source, including its bibliography.
- `README.md`: this document.
- `Makefile`: optional build and cleanup targets.

No external images, bibliography database, fonts, or repository checkout are required.
The document uses fonts supplied by the TeX distribution; no font files are bundled.

## Principal results

Work in an outer universe N of ZFC with a parameter-definable transitive inner
universe M of ZFC containing the same ordinals. All external cardinalities,
parameter sets, and types are measured in N. Let K = No^M and C = K[i].

1. For every uncountable N-cardinal kappa, K is kappa-saturated as an ordered
   field if and only if N has no new ordinal-valued sequences over M of length
   less than kappa. A stronger equivalent interpolation criterion needs only
   one side of a set-sized cut to have size less than kappa (Theorem 1.1,
   proved in Section 5).
2. The first new ordinal-sequence length delta is regular in both universes,
   and K has a gap of exact cofinality pair (delta, delta), with no smaller
   side of a set-character gap (Proposition 5.2 and Theorem 5.3).
3. K is omega-saturated exactly when the extension adds no reals
   (Theorem 6.1). Prikry forcing separates this from omega_1-saturation.
4. C in the pure field language remains saturated over every N-set of
   parameters. Adding conjugation restores the saturation spectrum of K
   (Theorems 7.1 and 7.3).
5. For a ground uncountable regular cardinal kappa that remains a cardinal,
   the old birthday fragment No_{<kappa} is externally kappa-saturated exactly
   when kappa remains regular and all binary signs shorter than kappa remain
   old (Theorem 8.1).
6. An explicit set-complete class Boolean algebra densely contains the
   reverse-simplicity sign tree. Requiring joins of all subclasses is
   impossible under Global Choice (Theorems 11.1 and 11.3).

## Verification and novelty status

The package supplies mathematical arguments, not a Lean formalization.
The source was compiled successfully with pdfLaTeX and latexmk. The PDF was
rendered and checked, with no undefined references or overfull boxes in the
final compilation log. Typesetting checks do not verify the mathematics.

The principal spectrum and decoder theorems are proposed contributions not
located in the consulted literature or specified repository review. This is
not a guarantee of historical novelty or an independent referee's certification.
Classical surreal facts, quantifier elimination, and standard forcing facts
are cited separately. The Boolean construction answers a precisely interpreted
question in Berenbeim's 2020 research notes, without claiming that it was still
unresolved elsewhere or that the construction is not folklore.

The repository file review was pinned to:

    VladimirReshetnikov/Surreal
    4f2645599121fa872c7104995e47f86f0382351f

Code searches used the connector's default-branch index. Appendix A records the
read/search scope and its limitations. The repository was not modified or
independently built. Appendix B lists dependencies and proof obligations.

## Building

Use a reasonably current TeX Live or MiKTeX installation with the `newtx`,
`amsmath`, `mathtools`, `geometry`, `microtype`, `booktabs`, `enumitem`, `xurl`,
`fancyhdr`, `hyperref`, and `cleveref` packages and their dependencies.

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without latexmk, run the following command three times to settle the table of
contents, citations, and cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The same commands work from PowerShell when the TeX tools are on PATH.
On systems with Make, `make` builds the PDF and `make clean` removes auxiliary
files while preserving the PDF.
