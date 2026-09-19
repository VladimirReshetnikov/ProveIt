# Finite Hankel Certificates for Three Somos-8 Conjectures

Research report prepared for Vladimir Reshetnikov — 19 September 2026.

## Result

The article proves the Somos-8 bilinear assertions in Conjectures 11, 12,
and 13 of Paul Barry's *Conjectures on Somos 4, 6 and 8 sequences using
Riordan arrays and the Catalan numbers* (arXiv:2211.12637).

The proof imports Andrew Hone's published genus-two Hankel theorem
(Theorem 5.4 of arXiv:1907.05204v3), then supplies:

- a binomial translation into the seven-parameter moment class;
- a polynomial-minor specialization argument that remains valid on the
  degenerate coordinate locus relevant here;
- a finite-certification lemma that turns four symbolic rows into an
  all-index identity;
- twelve exact zero residuals and three nonzero integer rank witnesses.

This is not an argument that finite numerical testing proves an infinite
recurrence. The rank bound is the mathematical reason the finite certificates
suffice. The published structural theorem is not independently reproved here.

The results are denominator-cleared identities in Z[r], including exceptional
parameter values and sequences containing zero determinants. For Conjecture
13 the defining continued fraction is used: the source's separate Catalan
expression has a sign error, identified explicitly in the article.

Additional results for the Conjecture 12 family include two Somos-6
specializations, a positive finite coefficient formula, a decorated-plane-tree
interpretation, and an all-orders asymptotic expansion for its moments. These
are NOT claimed as asymptotics for the Hankel determinants.

No earlier proof of the three precise Somos-8 assertions was located in the
focused literature search. This is not exhaustive certification of novelty or
historical priority. External mathematical review remains appropriate.

## Files

- `article.pdf`: complete, typeset article.
- `article.tex`: standalone LaTeX source, including references.
- `build.sh`: compile the PDF without leaving auxiliary files in this folder.
- `code/verify_certificates.py`: exact verifier; Python standard library only.
- `code/cross_check_sympy.py`: independent SymPy moment and determinant check.
- `code/examples.py`: exact example sequences and high-precision numerical
  checks of the moment asymptotics.
- `data/certificates.json`: coefficient arrays, moments through index 20,
  Hankel polynomials through index 10, residuals, and rank witnesses.
- `data/numeric_audit.json`: 858 exact integer audits, over three families,
  parameters -5 through 7, and recurrence indices 7 through 28.
- `data/C12_r*_moments.txt`: moments through index 64, for r = 0, 1, 2, 3, 4.
- `data/C12_r*_hankels.txt`: Hankel determinants from index -1 through 32.
- `data/asymptotics_C12_r2.json`: high-precision constants and ratios for r = 2.

## Reproduce the mathematical certificates

Use Python 3.10 or later. From this folder:

```sh
python3 code/verify_certificates.py --audit
python3 code/examples.py
```

The verifier computes moments directly from the defining quadratic equation,
then computes the determinants by checked fraction-free Bareiss elimination.
It never generates the determinants using the conjectured Somos recurrence.
Every polynomial division is checked for exactness; nonzero residuals or
incorrect rank witnesses raise exceptions. The scripts write the data files
listed above, overwriting reproducible outputs in `data/`.

Expected summary: all 12 symbolic residuals vanish; all 3 rank witnesses are
nonzero; all 858 additional integer recurrence checks pass.

For a second determinant implementation:

```sh
python3 -m pip install sympy
python3 code/cross_check_sympy.py
```

The independent cross-check was run successfully with SymPy 1.14.0. SymPy is
optional: the primary certificate verifier has no third-party dependencies.
The cross-check regenerates moments and Hankel determinants using SymPy's
polynomial-ring and DomainMatrix implementations, and compares them with the
certificate data. It does not reprove Hone's external structural theorem.

## Compile the article

A TeX Live or MiKTeX installation with pdfLaTeX and common packages is needed,
including `newtx`, `amsmath`, `amsthm`, `mathtools`, `tcolorbox`, `microtype`,
`booktabs`, `fancyhdr`, `listings`, `hyperref`, and `bookmark`.

```sh
bash build.sh
```

The script runs pdfLaTeX three times in a temporary directory, copies the
resulting PDF here, and removes the temporary auxiliary files. Alternatively,
run `pdflatex article.tex` three times in this directory. No bibliography tool,
external illustrations, network access, or additional source files are needed.

## Conventions

The moments are `a_n = [x^n] g(x)`. The Hankel transform is
`h_n = det(a_(i+j))_(0 <= i,j <= n)`, with the empty determinant `h_-1 = 1`.
Thus `h_n` is a matrix determinant of size n+1, not size n.

JSON polynomial arrays list coefficients in ascending powers of r, including
`[0]` for the zero polynomial. Plain-text example files contain index-value
pairs with comment headers. All main proof data are exact integers; only the
asymptotic constants and their validation ratios use decimal approximations.

The package contains no downloaded third-party papers, font files, checksum
files, or LaTeX auxiliary files. References to the external mathematical inputs
are included in the article.
