# Shared coefficient positions and integral Pell carriers

Research contribution prepared for Vladimir Reshetnikov's ProveIt repository,
23 October 2026. The comparison is pinned to
`beb0192cb8dc36f78c369c080f2adfbc1887a486`, including packages 54–59 (wave 8).

Read **report.pdf** for the article; **report.tex** and the component
`section.tex` files are its complete editable LaTeX sources.

## Proved improvements

All rows below specify **one integer-coefficient polynomial equation**, with
the indicated domain. The primary domains are strictly positive integers.

| Equation | Variables | Exact total degree | Live binary operations |
|---|---:|---:|---:|
| Shared positions, primary | 9 positive | 1,675,396 | 458 |
| Shared positions, cheaper tradeoff | 9 positive | 1,738,228 | 457 |
| Shared positions, Sun finalizer | 10 unrestricted integers | 7,428,120 | 525 |
| Integral carriers, primary | 14 positive | 26 | 92 |
| Integral carriers, cheaper tradeoff | 14 positive | 30 | 85 |

The inspected package-59 nine-positive baseline is degree 1,910,404 in
473 operations. The package-55/59 fourteen-positive baseline is degree 52
in 79 operations. The new degree-26 point halves that degree and uses
thirteen additional gates. The fourteen-variable tradeoff improves degree
52 to 30 with six additional gates. The degree-24 fifteen-variable equation
and the 66-operation fifteen-variable equation retain their own advantages.

The ten-integer equation improves on package 59's degree 8,469,528 at 533
operations, and also improves on package 57's degree 8,317,400 at 544
operations. Package 54 retains a cheaper 513-operation point, at degree
25,838,224. These comparisons do not identify a single winner across all
measures of simplicity.

For each new equation on its stated domain, the ordinary mathematical proof,
composed with the named inherited native compiler and syntactic refutation
calibration, gives

    ZFC proves: (there is no solution) iff Con(ZFC).

This is a proof of the equivalence. It does not decide either consistency or
solvability. No global minimum, new smallest variable count, or new complete
Lean/Rocq or object-language ZFC certificate is claimed.

## The two ideas

**Shared coefficient positions.** Several target equations can reuse a kernel
position when they require the same complete fixed coefficient. Store the
coefficient once. Check every source interaction after that change. The primary
certificate represents 89 weighted source records with 84 unique positions,
reducing the convolution height from 2,161 to 1,873. Every one of the 22 target
identities is checked symbolically, including all 11,616 relevant coefficients.

**Successive congruence recovery.** Supply the formerly scaled coordinates X
and Y directly. An existing square equation first forces q^3 to divide Y.
A second integral root yields a congruence modulo 4qY, large enough to recover
the exact Pell index. After that recovery, the stronger modulus 4q^2Y forces
q to divide X. This removes the old index quotient without adding a witness
and keeps the equation small in degree. The order of the proof prevents
circular use of a divisibility condition that has not yet been established.

## Layout

- `report.tex`, `report.pdf`: main article and its compiled PDF.
- `nine/`: the primary nine-positive equation, the cheaper tradeoff,
  natural-coordinate companions, the exact finite source certificates,
  coefficient payloads and recipes, complete new proof, and finite checks.
- `pell/`: the two fourteen-positive equations, coefficient payloads and
  recipes, complete new proof, independent proof review, and finite checks.
- `sun/`: the ten-unrestricted-integer companion, exact source replacement,
  complete finalizer formulas, degree certificate, and finite checks.
- `baseline/`: exact pinned comparison READMEs, authenticated by Git blob
  and SHA-256 hashes in the provenance file.
- `verify_all.py`: integrated verification entry point.
- `VERIFICATION.json`: verification receipt from the delivered files.
- `PROVENANCE.json`: repository snapshot and comparison sources.
- `MANIFEST.sha256`: hashes of the released files other than the manifest.
- `LICENSE`, `NOTICE.md`: license and attribution.

The mathematical components use **two different complete native coefficient
tuples**. The nine-variable and Sun families retain source 31's original
tuple; the fourteen-variable family retains source 44's compact tuple. Do not exchange
individual ports. Intermediate registers are abbreviations, not additional
existentially quantified variables. Large fixed leaves do not depend on whether
ZFC has a refutation.

## Reproduce

The finite mathematical checks were tested with Python 3.12 and use only
its standard library:

```sh
python3 verify_all.py
```

The checker authenticates the release manifest, runs the component checks in
an isolated temporary copy, and records what was checked. It does not perform
an unbounded refutation search. Finite checks establish transcription,
polynomial identities, source certificates, exact degrees, counts, and fixed
data integrity; the universal solvability equivalence is established by the
written mathematical arguments and their named dependencies.

With a normal TeX Live or MiKTeX installation, compile the paper twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Rebuilding a PDF may change metadata and therefore its file hash. For changes,
work in a copy and refresh the manifest when deliberately making a new release.

## Integration and proof status

This archive is prepared for incorporation as a new contribution beside the
existing packages. No remote repository files were changed or published.
The root article includes further research questions and an explicit account
of the proof boundary. The independent reviews are reviews by separate
AI-assisted workers in this research session, not external human peer review.

The active ProveIt formalization has separate closed consistency equations.
Their theorems do not automatically certify these newly emitted smaller
circuits. A full formalization must join the exact coefficient bindings,
new reductions, native compiler, and object-language consistency statement.
