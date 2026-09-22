# Growth-Scale Rigidity for Surreal and Surcomplex Automorphisms

Research manuscript prepared with ChatGPT, dated 21 September 2026.

## Contents

- `article.pdf`: the 19-page typeset article.
- `article.tex`: complete standalone LaTeX source, including bibliography.
- `verify_identities.py`: exact finite checks using only Python's standard library.
- `verification_output.txt`: output of the included check run.
- `README.md`: this file.

## Principal results

Theorem 5.1 and Corollary 5.2 provide a negative answer to Question 5.4 in
Kaplan–Krapp–Serra, *Decomposing the automorphism group of the surreal numbers*,
arXiv:2509.22374v3: every exponential 1-automorphism of No is the identity.
The proof requires neither strong additivity nor pointwise fixation of R.

Theorems 4.1 and 4.4 establish the stronger ordered-exponential-field result:
a nonidentity exponential automorphism stabilizing a nontrivial convex
valuation induces cofinal and coinitial additive displacement on the value
group. Its action is faithful, also after any invariant nontrivial convex
coarsening. Coarsening stabilization is an explicit hypothesis.

Section 6 gives ordered value-group automorphisms with canonical Hahn-field
lifts but no exponential lift, including bounded-layer coefficient
reweightings and every positive rational dilation other than the identity.

Theorems 7.2 and 7.4 classify automorphisms of F(i) preserving logarithmic
modulus L(z)=log|z|. Their invisible value-group kernel consists exactly of
the identity and conjugation; fixing i removes the latter ambiguity.

## Build

Use a current TeX distribution with the usual AMS packages, newtx, geometry,
microtype, fancyhdr, hyperref, and cleveref:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex` repeatedly until references settle. There is
no external `.bib` file and no external figure dependency. Font packages
are standard TeX dependencies; no font files are distributed here.

## Exact finite checks

Python 3.10 or later, no third-party dependency:

```sh
python verify_identities.py
```

The included run passes all seven test methods. Each randomized method
uses a deterministic seed and 300 exact-rational trials. These test the
twisted product identity, its two-probe inequality, finite Hahn
substitutions, bounded-layer/coarsening analogues, the rational-dilation
polynomial identity, and multiplicativity of the squared complex modulus.

These tests are NOT an implementation of No, do NOT verify infinite
summability, and do NOT formally certify the article's theorems. The
mathematical arguments are in the article.

## Provenance and scope

Repository documentation was inspected at commit
`aa846271b4dcae2c055b216126a87210292ec19b` of
`VladimirReshetnikov/Surreal`. No repository files were changed.

The named question was checked in arXiv:2509.22374v3, submitted 23 April
2026, whose PDF is dated 27 April 2026; Question 5.4 is on source page 10.
The exact source version matters: the question is attributed to that
version, not assumed from a secondary summary.

This is an unrefereed research manuscript, not a formally certified or
peer-reviewed publication. Targeted literature searches did not locate the
stronger results in the stated form, but exhaustive priority is not
claimed. The article does not classify the full image of the exponential
automorphism group in the ordered value-group automorphism group.
