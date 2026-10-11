# Exact Polylogarithm Parity, Harmonic-Tail Reconstruction, and Higher Polygamma Moments

Research continuation for Vladimir Reshetnikov and the ProveIt project, 11 October 2026.

## Start here

The main deliverables are the PDF and the self-contained TeX file named
`ProveIt_Polygamma_Tail_Identities_2026-10-11`. The modular source is
`article.tex`, with its sections under `sections/` and its bibliography in
`references.tex`. The PDF contains the complete statements, proofs, source
audit, exact tables, and further research agenda.

The baseline repository revision is:

```
f7e35be357654198c1546fd40f363694c5bcc2cc
```

The source is https://github.com/VladimirReshetnikov/ProveIt, specifically
`Analysis/Polylogarithms/docs/manuscript` and `docs/incoming`.

## Principal results

1. Proof of the first-q moment conjecture for all adjacent even tail orders
   p=q-2>=2, with an exact nonzero determinant and ordinary convergent
   reconstruction identities. The general larger-gap families remain open;
   some isolated larger-gap pairs were already proved in the source.
2. Exact proof and simplification of the recorded Gaussian Family-2 equation,
   through a self-contained implementation of established bicolored parity.
3. All polygamma-square coefficients and the complete digamma–trigamma sector
   of the Gamma differential normal forms, including a Shi generating function.
4. Exact original-coordinate finite parts of all quadratic integer-order
   Hurwitz products, all their order jets, and all quadratic products of
   positive argument derivatives of generalized Stieltjes constants.
5. An absolutely convergent, unsubtracted Mittag–Leffler theorem for every
   derivative-containing digamma differential polynomial, with anchored
   antiderivatives and finite convergent MZV derivative coordinates.
6. An explicit sixth digamma moment, including the fully specified mixed
   constant Omega_5 and its 17 individually convergent MZV germs.

General parity, the abstract functional-monomial normal form, the classical
Hurwitz product kernel, and the incoming all-order Gamma bridge receive their
prior attribution. This is not a claim to have proved S6, revised S8, or the
full unequal-tail conjecture. Formal ranks are not independence claims.

## Build the PDF

With a standard TeX Live installation including latexmk:

```bash
python code/build_article.py
```

Equivalently:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build script writes the detailed compiler output to `qa/build_stdout.log`
and prints meaningful warnings. The required TeX packages are ordinary
TeX Live packages: amsmath, amssymb, amsthm, mathtools, mathrsfs, lmodern,
geometry, microtype, booktabs, longtable, tabularx, xcolor, enumitem, fancyhdr,
xurl, and hyperref. The self-contained TeX file can also be compiled directly.

## Reproduce the calculations

The calculation environment used Python 3, SymPy 1.14.0, and mpmath 1.3.0.
Install the two Python dependencies if needed:

```bash
python -m pip install -r requirements.txt
```

Run the finite exact checks and regenerate the coordinate data:

```bash
python code/run_verification.py --exact
```

Run the complete reproducible suite, including the numerical diagnostics:

```bash
python code/run_verification.py --full
```

The full suite includes 115-digit mixed-coordinate summation and independent
quadrature. It is intentionally more expensive than the exact-only run.
The completed results are already supplied under `verification/`.
Changing a working precision does not create a rigorous interval enclosure;
the recorded residuals are diagnostic evidence. The arbitrary-order results
are justified by the article's written proofs.

The main production module is `code/differential_normal_form.py`. Its
normal-form algorithm uses exact rational coefficients. The published tables
cover weights 2–10, and an independent sector comparison covers weights
0–16. The current symbolic arrays provide u_0 through u_24 and zeta symbols
through zeta(30); extend those arrays before requesting larger symbolic
expressions or endpoint tables. This finite implementation choice is not a
restriction on the proved algorithm.

`code/mixed_sixth.py` produces both the 18-term grouped first-coordinate
representation and the 17-term individually convergent representation.
In the latter JSON data, `spectral_parameter_slot` is zero-based. A slot of
1 means the second zeta coordinate is differentiated; it must not be treated
as a first-coordinate derivative.

## Contents and integration

- `sections/`: complete modular mathematical article.
- `code/`: production algebra and independent verification programs.
- `data/`: exact normal forms, primitives, boundaries, and spectral words.
- `verification/`: completed exact and numerical records.
- `integration/`: source/archive audit, claim ledger, and proposed source changes.
- `qa/layout_report.json`: final rendering and layout check summary.
- `MANIFEST.sha256`: checksums of the packaged files other than the manifest itself.

The package contains no modified checkout and no copies of the six incoming
archives. Their names and hashes are in `integration/incoming_audit_summary.json`.
Suggested repository integration is described in `integration/PROPOSED_CHANGES.md`.
No repository publication or commit is part of this delivery.
