# Bounded-Support Hahn Arithmetic
## Cofinal descent, optimal support thresholds, and maximal transcendence

Research draft prepared with ChatGPT, 22 September 2026.

The article is 24 pages, including its title page, contents, appendices, and
bibliography. The mathematical core is unconditional relative to the named
standard Hahn-field and Conway-normal-form foundations. Appendix A is an
explicitly conditional GCD reduction, not an unconditional solution of a
historical open problem. No peer review or Lean verification is claimed.

## Main results

For a characteristic-zero field K and a nonzero set-sized ordered abelian
exponent group G, let B_G(K) be the ring of Hahn series whose support is bounded
above in G, and let F_G(K) be its fraction field. With kappa = cf(G), the article
constructs 2^kappa series algebraically independent over F_G(K). They all have
positive integer coefficients and the same positive cofinal support of order
type kappa. Both the support cardinality and the support order type are optimal.
Every valuation ball contains such an independent family.

A separate theorem proves simultaneous coefficient and exponent descent:
when K is a subfield of L and H is a nonzero cofinal subgroup of G, K((t^H))
and F_G(L) are linearly disjoint over F_H(K), in their specified common Hahn
field. In characteristic zero, cofinality is also necessary. Relation ideals
and finite algebraic degrees are preserved.

The article obtains exact transcendence degrees for real-exponent fields and
for explicit groups of every infinite regular cardinality. It supplies actual
surreal witnesses via Conway normal form. It also characterizes when the
bounded-support ring is a field and describes its units through the highest
Archimedean quotient when applicable. The distinctions between an intrinsic
Hahn valuation topology, Hahn summation, and the full surreal fine topology
are retained throughout.

## Files

- `article.pdf`: the complete typeset article.
- `article.tex`: self-contained LaTeX source, with an internal bibliography.
- `coefficients.py`: an explicit computable countable coefficient code and
  finite factorial-support prefixes; Python standard library only.
- `verify.py`: exact finite regression checks of the proof mechanisms.
- `verification.json`: the delivered run, 3,163 assertions in 12 groups, all
  passed. Finite checks are not proofs of the transfinite theorems.
- `build.py`: three-pass PDF builder, with shell escape disabled.
- `research_audit.md`: repository and literature review scope, dependencies,
  novelty boundaries, and the conditional appendix's status.
- `build_audit.json`: delivered PDF build and layout checks.
- `manifest.json`: SHA-256 digests of the other delivered files.

## Rebuild the PDF

Use Python 3.10 or later and a TeX Live or MiKTeX installation providing
pdfLaTeX, AMS packages, New PX text/math, geometry, microtype, booktabs,
tabularx, longtable, array, xcolor, enumitem, fancyhdr, needspace, titlesec,
hyperref, and bookmark. Fonts are supplied by the TeX installation; no font
files are distributed in this archive. No network access or external images
are needed by the document.

From this directory run:

```sh
python build.py
```

The builder places intermediate files in `.build/` and copies the successfully
built PDF to `article.pdf`. Alternatively, run pdfLaTeX three times yourself:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error article.tex
```

With the delivered TeX installation, `epstopdf` prints a harmless warning that
shell escape is disabled. This document has no EPS graphics and does not need
conversion. The final build had no overfull/underfull boxes or unresolved
references or citations. PDF byte-for-byte reproducibility is not claimed:
PDF timestamps and TeX versions can change the binary output.

## Rerun the finite checks

No third-party Python packages are needed:

```sh
python verify.py --output verification-local.json
python coefficients.py
```

The checker uses exact integers and rational numbers, not floating-point
approximations to infinite series. The random seed is fixed at 20260922.
`verification-local.json` avoids overwriting the delivered run record.

The abstract coding lemma uses a bijection with finite tables plus a
repetition coordinate. The executable countable implementation instead uses
an explicit *surjective* code and a repetition coordinate. It has the same
required property: every prescribed finite positive-integer pattern occurs
at infinitely many indices. It does not enumerate all subsets of the natural
numbers. It asks finitely many membership questions of the supplied subset
predicate for each requested coefficient. Its finite prefixes do not decide
algebraicity or certify an infinite independence statement.

## Novelty and verification boundary

The primary proposed contributions are the support-optimal independent-family
theorem and the cofinal coefficient–exponent linear-disjointness theorem.
Earlier published nonrationality/cofinality obstructions are explicitly
credited, not repackaged as new. These formulations were not identified in the
reviewed repository descriptions and targeted primary literature. That is not
an exhaustive priority determination. See `research_audit.md` and Appendix B.

The normal-form realization concerns named set-sized subfields of the surreal
and surcomplex numbers. None of the witnesses is asserted transcendental over
all surreal or all surcomplex numbers. A family of the maximum possible
cardinality is not automatically a transcendence basis.
