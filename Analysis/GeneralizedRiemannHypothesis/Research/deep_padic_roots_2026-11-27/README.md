# Exact exponent compression and positive-filter rigidity

Research prepared for Vladimir Reshetnikov, November 27, 2026.

## Main deliverables

- **deep_padic_roots.pdf** — complete proof of a uniform exponent-transport theorem, finite exact lattice and determinant formulas, and the sharp eight-term two-adic classification.
- **positive_filter_rigidity.pdf** — a companion theorem giving the Hessian of optimal positive-filter width at every distinct strictly positive mirror spectrum.
- **main.tex**, **main_body.tex**, **companion_filters.tex**, **filters_body.tex**, and **preamble.tex** — complete editable LaTeX sources.
- **checks/** — exact finite verifiers, deterministic transport checks, a symbolic/high-precision companion check, and figure-generation code.
- **data/** — complete outputs, including all 165 residue-profile certificates and an independent computation of every profile.
- **figures/** — exact Newton-polygon diagram in PDF and PNG.
- **FORMALIZATION.md** — mathematical dependency and verification boundary.
- **SOURCE_MAP.md** — pinned source revision, inspected sections, and primary literature.

## Results

For a prime p and t >= 2, define D as the maximum base-p digit sum of the integers 0,...,t-1, A = ceil((D-1)/(p-1)), and P = p^A. Two t-element exponent supports with the same residue multiset modulo P admit a unique invertible rational coefficient map matching their first t Euler derivatives at one. This map preserves the complete multiset of geometric root depths strictly greater than 1/(p-1), with multiplicity, including a root at one. It also preserves the first residue of a root at each such depth. It need not preserve individual roots or fields of definition.

Every support is therefore equivalent, for this problem, to a canonical support of exponent diameter at most (t-1)P. Exact lattice formulas compute the sharp open and closed counts. An equivalent finite lower-envelope formula describes the entire depth profile. Integer full-support witnesses with simple roots in the disk attain the extrema; after factoring the forced monomial, they may be made irreducible.

For t=8 and p=2, the complete classification depends only on exponent multiplicities nu_0,...,nu_3 modulo four. Put e=nu_0+nu_2. The sharp open-disk maximum is:

- 9 if e is congruent to 2 modulo 4;
- 7 if e is congruent to 0 modulo 4 and all four multiplicities have the same parity;
- 8 otherwise.

The 165 profiles divide into 42, 23, and 100 cases respectively. The global maximum is **nine**, even with all coefficients required to be integers and all counted roots required to be distinct.

An explicit eight-term witness is

    183 X^10 - 235 X^8 + 54 X^6 - 6 X^4
        - 128 X^3 + 3 X^2 + 128 X + 2049.

Its translated Newton polygon has vertices (0,11), (9,1), (10,0). It has nine roots at depth 10/9 and one at the excluded depth-one boundary. A short polynomial Bezout identity modulo seven certifies squarefreeness.

The companion result expresses the width Hessian as a positive weighted-variance integral. Its kernel is exactly the tangent space preserving mirror symmetry. For three frequencies, one explicit specialization is

    B(1/2+epsilon, 1-2 epsilon, 3/2+epsilon)
        = 3 pi + 6 pi epsilon^2 + O(epsilon^3).

The companion includes the general three-frequency curvature, its coalescence expansion, and its divergence at the boundary where optimal weights vanish.

## Status and limits

These are unconditional mathematical extensions of two questions in the inspected ProveIt article. They do not use RH or GRH as hypotheses. The main theorem answers the source's finite-residue-data question for arbitrary term count; the companion answers the distinct-real-spectrum part of its general mirror-Hessian question.

This archive does **not** claim a solution to a prominent classical conjecture, a complete proof audit of the repository's RH/GRH development, or certified global publication priority. Primary-source checks distinguish the structural transfer from classical degree-independent root bounds. In particular, roots here are geometric roots in an algebraic closure; the fixed-local-field fewnomial problem remains different.

The general results have written proofs and independent review within the research session. The eight-term upper bound additionally uses a complete finite exact computation. There are no new Lean files and no claim that the results have passed the Lean kernel. Numerical checks in the companion are illustrations, not proof certificates.

## Reproduce the exact computations

Python 3.12, SymPy 1.14.0, and mpmath 1.3.0 were used. The independent DVR and transport checkers use only the Python standard library. The supplied figure needs matplotlib only if regenerated.

From this directory:

```sh
make checks
```

This regenerates the HNF certificates, independent DVR output, a case-by-case comparison, 256 deterministic transport examples, and the companion checks. The comparison checks every maximum, every prefix-rank increase list, and every lattice determinant valuation, rather than only the final histogram.

For a quick exact verification without third-party Python packages:

```sh
python3 checks/independent_dvr_check.py
python3 checks/transport_check.py
python3 checks/witness_audit.py
```

The last command checks the explicit polynomial translations, Newton polygons, squarefreeness certificate, and coverage of the stored classification.

## Rebuild the papers

A TeX Live installation with latexmk, amsmath, amsthm, mathtools, lmodern, microtype, fancyhdr, tocloft, xurl, and hyperref is sufficient. The supplied figure is already present.

```sh
make papers
```

To regenerate the figure before rebuilding:

```sh
make figure
make papers
```

The main paper is built from `main.tex` with job name `deep_padic_roots`; the companion is built from `companion_filters.tex` with job name `positive_filter_rigidity`.

## Certificate schema

Each entry in `data/lattice_certificates.json` specifies the residue multiplicities, canonical exponent support, exact integer HNF basis, determinant valuation, and ordered prefix-rank increments. Each entry in `data/independent_dvr_results.json` gives the same support and rank-increase indices obtained by rational elimination over the local ring Z_(2). The output `data/certificate_comparison.json` records their full agreement.

The HNF bases are finite integer matrices; all local membership and determinant comparisons use exact rational arithmetic. No floating-point root approximation enters the two-adic classification or either explicit witness.

`SHA256SUMS` records every packaged file except itself. After extraction, it can be checked with `sha256sum -c SHA256SUMS` from this directory.
