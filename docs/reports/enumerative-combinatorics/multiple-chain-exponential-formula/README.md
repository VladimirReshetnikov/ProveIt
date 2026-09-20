# Multiple-chain preorder polytopes

## Main result

This package gives a proposed complete proof — in fact two independent proofs —
of the conjectural generating-function identity in Section 9.5 (printed page 24)
of Christos A. Athanasiadis and Frédéric Chapoton, *Polytopes and posets
associated to preorders*, arXiv:2605.26916v1.

Let H[n,d](t) count nonnegative integer arrays with n blocks of d coordinates,
subject to a total of at most d*r in the first r blocks; t marks the number of
nonzero coordinates. The proved identity is

    sum(n>=0) H[n,d](t) z^n
      = exp(sum(m>=1) (z^m/m) sum(j=0..d*m) binom(d*m,j)^2 t^j).

More generally, replace the budget d*r by c*r. The bridge polynomial becomes

    C[m;d,c](t) = sum(j>=0) binom(d*m,j) binom(c*m,j) t^j.

The proofs are coefficientwise and valid for every integer d>=1, c>=0.

- **First proof** (Section 2): a two-subset encoding of the original lattice
  points turns them into nonnegative *excursions* with the bounded
  Laurent-polynomial symbol (1+u)^c (1+t/u)^d; the logarithm of the excursion
  series is the constant term, evaluated by the binomial theorem.
- **Second proof** (Section 3): the original coordinate slack process gives
  *meanders* with the Laurent-series symbol u^c ((u+t-1)/(u-1))^d in
  Q[t]((u^-1))[[z]]; the positive part is projected first, u=1 is substituted
  afterwards, and stars and bars produces the type-B Narayana polynomial.

The two proofs use different walks, different symbols, different rings and
different boundary conditions. Both are kept.

## Provenance

This package is the merger of two independently prepared research packages,
both dated 20 September 2026, which targeted the same identity:

- `enumerative-combinatorics/multiple-chain-exponential-formula` (this
  directory, the base of the merge) contributed the rectangular theorem, the
  subset-encoding/excursion proof, the support duality, the Ehrhart
  evaluation, the Stieltjes moment section, and the exact variance with its
  constant-order correction `kappa_d`.
- `enumerative-combinatorics/multiple-chains-exponential-identity` contributed
  the slack-meander proof in its cleanest ring, the endpoint refinement, the
  stars-and-bars lemma, the gamma integrality and strict-positivity arguments,
  the fixed-support polynomiality theorem, the mixed-block-size theorem with
  its order-dependence counterexample, the Lagrange-inversion Narayana row, and
  a verifier suite over a deeper parameter range.

Section 1.2 of the article states this provenance in full, and Section 1.5
lists the eleven results that are deliberately kept in two versions, with one
sentence each on what the duplication buys.

## Read first

- `article.pdf`: the 30-page article, including all proofs and references.
- `article.tex`: its self-contained LaTeX source; no external figures or `.bib`
  file are needed.
- `STATUS.md`: exact claim boundaries and verification status.
- `sources.md`: problem provenance, literature/priority limitations, and the
  relation to the supplied manifest.

Besides the two proofs, the article derives rectangular support duality, exact
recurrences and partition formulas, Ehrhart evaluations, an algebraic
root-of-unity product with two proofs of the degree bound 2^d, a double-chain
quartic with two elimination certificates, a block-boundary path model and an
algebraic derivation of the already known gamma positivity (with integrality
and strict positivity), exact polynomiality in n at each fixed support size,
a mixed-block-size identity summed over orders, Stieltjes moments, explicit
asymptotics with two expressions for the boundary constant, an exact support
variance, and a central limit theorem with its variance constant.

## Exact verification

From this directory, with Python 3.10 or later:

```sh
python code/verify.py
```

No third-party Python package is required for this command, no floating-point
arithmetic is used, and the checks are raised through an explicit `require()`
rather than `assert`, so they remain active under `python -O`.

The script runs **two separate suites**, which are deliberately not fused:

- **Suite 1 (rectangular)** compares coordinate dynamic programming,
  subset-walk dynamic programming and the exponential recurrence for
  **315 parameter triples** (1<=d<=5, 0<=c<=6, 0<=n<=8), visits 34,689
  feasible arrays exhaustively in 48 small cases, and checks 225 duality
  instances, 54 gamma path expansions, 54 exact rational variance identities,
  the quartic through degree 16 in z, and the four double-chain rows printed in
  the source. The subset-walk DP is the only computational witness of the
  encoding used by the first proof, and this is the only data with c != d.
- **Suite 2 (diagonal, deeper)** compares a block-weight slack dynamic program
  with the recurrence for **104 complete polynomials** (1<=d<=8, 0<=n<=12),
  re-enumerates every individual coordinate vector in the 28 cases with
  d*n<=8, verifies the endpoint-refined factorization in 112 cases at
  t in {0,1,2,7}, reconstructs the gamma basis on all 104 rows, confirms the
  fixed-support degree and leading coefficient by finite differences in 40
  cases, checks the first two support-coefficient formulas on all 104 rows,
  re-checks the quartic coefficientwise in t, and verifies the mixed-size
  identity over all 121 ordered compositions with parts in {1,2,3} and at most
  four blocks (35 multiplicity vectors), recording the order-dependence
  counterexample.

Results are written to `results/` by default; `--output DIRECTORY` (or `--out`)
redirects them. All generated coefficient arrays use increasing powers.

Finite checks corroborate the proofs; they do not certify all parameters.

## Optional symbolic and numerical checks

Install the exact versions recorded in `requirements-optional.txt`, then run:

```sh
python code/derive_quartic.py
python code/symbolic_certificate.py
python code/asymptotics.py
```

The first two compute two *different* resultants with SymPy, eliminating
different pairs; the second reports that its difference from the printed
quartic is the zero polynomial, not a truncated series. The third compares
exact integer counts, and exact rational means and variances, with the proved
asymptotic expressions using mpmath at 80-digit working precision; it also
evaluates the boundary constant twice, once as a finite radical product and
once as a convergent exponential sum, and checks that the two agree. It
accepts `--maximum N` (default 400) and `--output DIRECTORY`. These numerical
comparisons are not interval-certified.

## Rebuild the article

A standard TeX Live or MiKTeX installation with the packages in `article.tex`
is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

`build.sh` performs the equivalent two `pdflatex` passes, and a small optional
`Makefile` provides the same commands. Neither is required on Windows. The
exact Python, SymPy, mpmath and pdfTeX versions used for this package are in
`results/environment.json`, and `results/pdf_validation.json` records the
build audit.

## Manifest and licensing

`context/manifest.tex` is an unchanged copy of the supplied manifest. The two
merged packages shipped byte-identical copies of it; only this one is kept.
`manifest-entry.tex` is a proposed addition for the user's existing `\entry`
macro; it is an include fragment, not a standalone document. No repository or
original manifest was edited, and this package contains no checksum manifest
of its own files.

The generated text and code are released under MIT-0 (`LICENSE`). The supplied
manifest already carries an MIT-0 SPDX header. Third-party papers are cited,
not redistributed. No font files are included.
