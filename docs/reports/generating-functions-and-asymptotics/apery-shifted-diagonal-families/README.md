# Three OEIS conjectural families for Apéry numbers

**Date:** September 20, 2026.

This archive contains a self-contained article proving the entire shifted-diagonal
zeta(3) family explicitly labeled conjectural in OEIS A143007, and both the
superdiagonal and subdiagonal zeta(2) families explicitly labeled conjectural in
OEIS A108625 at consultation. Every nonnegative integer shift is covered.

The arrays extend the classical Apéry sequences A005259 and A005258. The proof
uses explicit finite telescoping certificates, four-corner contiguity relations,
and rational path-independent sums. It also proves signed error bounds, shifted
cubic recurrences, and sharp leading error asymptotics for all three families.

## Main deliverables

- `article.pdf`: typeset mathematical article.
- `article.tex`: complete LaTeX source, with an embedded bibliography.
- `verify.py`: standard-library-only exact verification and certificate generator.
- `verification_report.txt`: the actual output of 25,840 successful exact checks.
- `certificates.json`: full rational interval endpoints and certified decimal prefixes.
- `convergence_table.csv`: exact certificate widths and common-digit counts.
- `array_sample.csv`: small square-array values (not flattened OEIS indices).
- `check_symbolic.py` and `symbolic_report.txt`: optional SymPy verification of seven
  rational-function identities, with actual results.
- `diagnostics.py` and `asymptotic_diagnostics.txt`: optional mpmath comparisons of
  leading asymptotic formulas at 420 decimal working digits.
- `source_audit.md`: precise OEIS targets and a historical-priority caveat.
- `Makefile`: compilation and verification commands.
- `requirements-optional.txt`: versions used for the optional checks.

## Reproduce the exact checks

Use Python 3.10 or later:

```sh
python3 verify.py
```

The program uses exact integer arithmetic and `fractions.Fraction`; it does not
call a numerical zeta function or access the network. It regenerates its report,
JSON certificates, and CSV tables in its own directory. A failed test raises an
exception. The random-path tests use the fixed seed 20260920.

The checks cover two independent definitions of the arrays, contiguity, square
closure, all displayed numerical examples, individual finite telescoper terms,
finite diagonal identities, random lattice paths, and recurrences. The exact
bounds prove the rational enclosures; the finite regression tests themselves do
not prove the infinitely quantified mathematical results.

## Rebuild the PDF

A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages,
mathtools, microtype, geometry, booktabs, xcolor, fancyhdr, and hyperref suffices:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively use `make pdf` and `make verify`. Run pdfLaTeX again if it requests
another cross-reference pass. The supplied PDF was rendered and visually checked;
the final compilation had no overfull-box or undefined-reference warnings.

## Optional independent checks

```sh
python3 -m pip install -r requirements-optional.txt
python3 check_symbolic.py
python3 diagnostics.py
```

The optional diagnostics are not the rational certificates. They use high-
precision numerical values of zeta(2) and zeta(3) only to check the behavior of the
asymptotic formulas. The article proves those asymptotic formulas separately.

## Reading the certificates

Every JSON record contains an exact lower and upper rational endpoint, written
as decimal numerator/denominator strings. The endpoints enclose zeta(2) or
zeta(3) by the article's proved bounds. A displayed count `d` of certified decimal
places means integer arithmetic verified

    floor(10^d * lower) == floor(10^d * upper).

This is a certification of the decimal prefix, not merely an estimate from the
interval width. At N=60 and k=0, the files certify 180 decimal places for zeta(3)
and 124 for zeta(2). All twelve supplied certificates have at least 120 places.

## Scope and historical status

The OEIS labels were checked on September 20, 2026. This project proves formulas
listed there as conjectural; it does not claim that the identities have never
previously been proved or that the discrete conservative-field method is new.
Ofir David's 2023 conservative-matrix-field paper contains closely related
structures and conjugate polynomials, which the article explicitly acknowledges.
The proof here is self-contained at the level of finite binomial sums, elementary
series estimates, and (for the optional sharp asymptotics) Stirling's formula.

No supercongruence or irreducibility conjecture is claimed to be resolved. No
proof-assistant formalization or independent peer review is claimed. No OEIS
edit or submission has been made. No third-party paper, complete OEIS page, or
font file is included in this archive.
